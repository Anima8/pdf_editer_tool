import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, Scale, HORIZONTAL, StringVar, OptionMenu
from tkinter.colorchooser import askcolor
import fitz  # PyMuPDF
from PIL import Image, ImageTk, ImageDraw, ImageFont
import os
import platform
import io
import copy
import math 
import threading 

# PDF編集アプリケーションのメインクラス
class PDFEditorApp:
    def __init__(self, root):
        self.root = root
        root.title("PDF編集ツール") # バージョン更新
        root.geometry("1300x780") # ウィンドウの高さを少し増やす

        self.pdf_path = None
        self.doc = None
        self.current_page_index = 0
        self.page_image_pil = None 
        self.page_image_tk = None
        # self.page_image_pil_base = None # キャッシュ戦略変更のためコメントアウト

        self.annotations = []
        self.selected_ann = None
        self.canvas_item_to_ann = {}

        self.drag_mode = 'none'
        self.drag_start_x = None
        self.drag_start_y = None
        self.original_ann_coords_canvas = None
        self.initial_pdf_coords_for_move = None 
        self.current_drawing_points_canvas = []
        self.temp_canvas_item_id = None

        self.original_pdf_coords_for_resize = None
        self.original_shape_specific_data_for_resize = None

        self.zoom_factor = 0.8
        self.selected_rect_color = "red"
        self.default_text_box_outline_color = "blue"
        self.mask_color = "black"
        self.white_mask_color = "white"
        self.redaction_color = "lightgrey"
        self.RESIZE_HANDLE_SIZE = 10

        self.font_cache = {}
        self.undo_stack = []
        self.redo_stack = []
        self.max_undo_depth = 20

        self.last_highlighted_item_id = None
        
        self._rendered_page_cache = {} 
        self._page_cache_lru = []
        self.MAX_PAGE_CACHE_SIZE = 5 
        self._dirty_pages = set()

        self.modes_list = [
            ("枠選択/操作", "select"), ("テキスト枠", "textbox"),
            ("矩形描画", "draw_rectangle"), ("楕円描画", "draw_oval"),
            ("直線描画", "draw_line"), ("フリーハンド描画", "draw_freehand"),
            ("画像挿入", "insert_image") 
        ]
        self.display_to_value_map = {display: value for display, value in self.modes_list}
        self.value_to_display_map = {value: display for display, value in self.modes_list}

        self._setup_menu()
        self._setup_left_panel()
        self._setup_right_panel()
        self._bind_events()

        self._save_state()
        self._update_undo_redo_buttons()

    def _setup_menu(self):
        menubar = tk.Menu(self.root)
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="ファイル", menu=file_menu)
        file_menu.add_command(label="PDFを選択", command=self.select_pdf)
        file_menu.add_command(label="PDFをクリア", command=self.clear_pdf_selection)
        file_menu.add_command(label="PDFを再読み込み", command=self.reload_pdf)
        file_menu.add_command(label="PDFを保存 (Ctrl+S)", command=self.save_pdf)
        file_menu.add_separator()
        file_menu.add_command(label="終了", command=self.root.quit)

        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="ヘルプ", menu=help_menu)
        help_menu.add_command(label="バージョン情報", command=lambda: messagebox.showinfo("バージョン情報", "PDF編集ツール v1.0"))
        help_menu.add_command(label="操作方法", command=self._show_help_dialog)
        self.root.config(menu=menubar)

    def _show_help_dialog(self):
        help_text = """
PDF編集ツール 操作方法

1. ファイル操作 (メニューバー「ファイル」から):
   - PDFを選択/クリア/再読み込み/保存
   - 終了

2. PDFツール (左パネル):
   - PDF分割: 指定ページ範囲を新規PDFとして保存。
   - PDF結合: 複数のPDFを結合。
   - ページ回転: 現在のページを90度ずつ回転させます。
   - 元に戻す (Ctrl+Z / Cmd+Z): 直前の操作を取り消します。

3. ページと表示 (左パネル):
   - ページ移動、プレビュー倍率調整。

4. モード選択 (左パネル プルダウン):
   - 枠選択/操作: 図形を右クリックで選択、左クリックでリサイズ、右クリック長押しで移動。
   - テキスト枠: マスキングや文字追加のベースとなる矩形領域を作成。
   - 矩形/楕円/直線/フリーハンド描画: 各図形を描画。
   - 画像挿入: 画像ファイルを選択し、クリックした位置に挿入。

5. 描画設定 (左パネル、各描画モード時):
   - 線の色、線の太さ。

6. 図形と枠の操作 (左パネル):
   - 枠削除: 選択した枠/図形を削除。
   - 文字削除: 選択した枠/図形をリダクション（黒塗り）する。
   - 黒色で塗りつぶし: 選択した枠/図形を黒色で塗りつぶす。
   - 白色で塗りつぶし: 選択した枠/図形を白色で塗りつぶす。
   - 枠選択解除: 現在選択されている枠/図形の選択を解除。
   - 選択範囲に追加/更新: 選択した枠/図形にテキストを画像として追加または更新。

ショートカット:
   - Ctrl+S (Cmd+S): 保存
   - Ctrl+Z (Cmd+Z): 元に戻す
        """
        messagebox.showinfo("操作方法", help_text)

    def _setup_left_panel(self):
        self.left_outer_frame = tk.Frame(self.root, width=450) # self.left_outer_frame として保存
        self.left_outer_frame.pack(side="left", fill="y", padx=10, pady=10)
        self.left_outer_frame.pack_propagate(False)

        self.left_canvas_widget = tk.Canvas(self.left_outer_frame, bg=self.root.cget('bg'))
        self.left_canvas_widget.pack(side="left", fill="both", expand=True)
        self.left_scrollbar = tk.Scrollbar(self.left_outer_frame, orient="vertical", command=self.left_canvas_widget.yview)
        self.left_scrollbar.pack(side="right", fill="y")
        self.left_canvas_widget.config(yscrollcommand=self.left_scrollbar.set)
        self.left_inner_frame = tk.Frame(self.left_canvas_widget, bg=self.root.cget('bg'))
        self.left_canvas_widget.create_window((0, 0), window=self.left_inner_frame, anchor="nw")
        self.left_inner_frame.bind("<Configure>", lambda e: self.left_canvas_widget.configure(scrollregion=self.left_canvas_widget.bbox("all")))
        
        self.left_canvas_widget.bind("<MouseWheel>", self._on_left_panel_mouse_wheel)
        self.left_canvas_widget.bind("<Button-4>", self._on_left_panel_mouse_wheel) 
        self.left_canvas_widget.bind("<Button-5>", self._on_left_panel_mouse_wheel)

        self.filename_label = tk.Label(self.left_inner_frame, text="(PDFファイル:未選択)", wraplength=430)
        self.filename_label.pack(pady=5)

        # --- PDFツール ---
        pdf_tools_frame = tk.LabelFrame(self.left_inner_frame, text="PDFツール", padx=10, pady=5)
        pdf_tools_frame.pack(fill="x", pady=5)
        tk.Button(pdf_tools_frame, text="PDF分割", command=self.split_pdf, width=12).grid(row=0, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="PDF結合", command=self.merge_pdfs, width=12).grid(row=0, column=1, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="ページ回転", command=self.rotate_current_page, width=12).grid(row=1, column=0, pady=2, padx=2, sticky="ew") # 新しいボタン
        self.undo_button = tk.Button(pdf_tools_frame, text="元に戻す (Ctrl+Z)", command=self.undo_action, state=tk.DISABLED, width=12) # 幅を調整
        self.undo_button.grid(row=1, column=1, pady=2, padx=2, sticky="ew") # 2列目

        # --- ページ操作 & ズーム ---
        page_zoom_container = tk.Frame(self.left_inner_frame)
        page_zoom_container.pack(fill="x", pady=5)
        page_frame = tk.LabelFrame(page_zoom_container, text="ページ操作", padx=10, pady=5)
        page_frame.pack(side="left", fill="x", expand=True, padx=(0,2))
        tk.Label(page_frame, text="ページ(0始):").grid(row=0, column=0, sticky="w")
        self.page_entry = tk.Entry(page_frame, width=4)
        self.page_entry.grid(row=0, column=1, padx=2)
        self.page_entry.insert(0, "0")
        tk.Button(page_frame, text="表示", command=self.go_to_page_from_entry, width=4).grid(row=0, column=2, padx=2)
        page_nav_frame = tk.Frame(page_frame)
        page_nav_frame.grid(row=1, column=0, columnspan=3, pady=2)
        tk.Button(page_nav_frame, text="<<前へ", command=self.prev_page).pack(side="left", padx=2)
        self.page_info_label = tk.Label(page_nav_frame, text="- / -")
        self.page_info_label.pack(side="left", padx=2)
        tk.Button(page_nav_frame, text="次へ>>", command=self.next_page).pack(side="left", padx=2)

        zoom_frame = tk.LabelFrame(page_zoom_container, text="倍率", padx=10, pady=5)
        zoom_frame.pack(side="right", fill="x", expand=True, padx=(2,0))
        self.zoom_scale = Scale(zoom_frame, from_=10, to=200, resolution=10, orient=HORIZONTAL,
                                label="%", command=self.set_zoom_factor_from_scale)
        self.zoom_scale.set(int(self.zoom_factor * 100))
        self.zoom_scale.pack(fill="x", expand=True, pady=0)
        
        # --- モード選択 (プルダウンメニューに戻す) ---
        mode_selection_frame = tk.LabelFrame(self.left_inner_frame, text="モード選択", padx=10, pady=5)
        mode_selection_frame.pack(fill="x", pady=5)
        self.draw_mode_var = StringVar(value="textbox") # デフォルトを「textbox」に変更
        initial_display_name = self.value_to_display_map.get("textbox", self.modes_list[1][0]) # 「テキスト枠」の表示名を取得
        self.dropdown_tk_var = StringVar(value=initial_display_name)
        self.mode_option_menu = OptionMenu(mode_selection_frame, self.dropdown_tk_var, 
                                           *[m[0] for m in self.modes_list], command=self._on_dropdown_select)
        self.mode_option_menu.config(width=20)
        self.mode_option_menu.pack(fill="x", padx=2, pady=1)

        # --- 描画設定 ---
        self.drawing_settings_frame = tk.LabelFrame(self.left_inner_frame, text="描画設定", padx=10, pady=5)
        self.drawing_settings_frame.pack(fill="x", pady=5)
        tk.Label(self.drawing_settings_frame, text="線の色:").grid(row=0, column=0, sticky="w", pady=2)
        self.line_color_var = StringVar(value="#000000")
        self.line_color_button = tk.Button(self.drawing_settings_frame, text="色選択", command=self._choose_line_color, width=8)
        self.line_color_button.grid(row=0, column=1, padx=2, pady=2)
        self.line_color_entry = tk.Entry(self.drawing_settings_frame, textvariable=self.line_color_var, width=10)
        self.line_color_entry.grid(row=0, column=2, padx=2, pady=2)
        tk.Label(self.drawing_settings_frame, text="線の太さ:").grid(row=0, column=3, sticky="w", pady=2)
        self.line_thickness_scale = Scale(self.drawing_settings_frame, from_=1, to=20, orient=HORIZONTAL, resolution=1, showvalue=True)
        self.line_thickness_scale.set(2)
        self.line_thickness_scale.grid(row=0, column=4, padx=2, pady=2, sticky="ew")
        self._update_drawing_settings_state()

        # --- 枠の操作 ---
        edit_frame = tk.LabelFrame(self.left_inner_frame, text="枠/オブジェクト操作", padx=10, pady=5)
        edit_frame.pack(fill="x", pady=5)
        edit_button_grid_frame = tk.Frame(edit_frame) 
        edit_button_grid_frame.pack(pady=5, fill="x")
        tk.Button(edit_button_grid_frame, text="枠削除", command=self.delete_selected_annotation, width=12).grid(row=0, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="文字削除", command=self.delete_image_in_selected_rect, width=12).grid(row=0, column=1, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="黒色で塗りつぶし", command=self.mask_selected_area_black, width=12).grid(row=0, column=2, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="白色で塗りつぶし", command=self.mask_selected_area_white, width=12).grid(row=0, column=3, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="枠選択解除", command=self.deselect_all_annotations, width=25).grid(row=1, column=0, columnspan=4, pady=2, padx=2, sticky="ew")
        
        # --- テキスト画像追加 ---
        text_image_frame = tk.LabelFrame(self.left_inner_frame, text="テキストを画像として追加/編集", padx=10, pady=5)
        text_image_frame.pack(fill="x", pady=5)
        tk.Label(text_image_frame, text="文字列:").grid(row=0, column=0, sticky="w", pady=2)
        self.text_to_add_as_image_entry = tk.Entry(text_image_frame, width=40) 
        self.text_to_add_as_image_entry.grid(row=0, column=1, columnspan=2, padx=5, pady=2)
        tk.Label(text_image_frame, text="フォントサイズ:").grid(row=1, column=0, sticky="w", pady=2)
        self.font_size_scale = Scale(text_image_frame, from_=10, to=100, resolution=1, orient=HORIZONTAL, label="", command=self.update_font_size_label)
        self.font_size_scale.set(100)
        self.font_size_scale.grid(row=1, column=1, padx=5, pady=2, sticky="ew")
        self.font_size_label = tk.Label(text_image_frame, text="100pt")
        self.font_size_label.grid(row=1, column=2, sticky="w", padx=2)
        tk.Label(text_image_frame, text="フォント:").grid(row=2, column=0, sticky="w", pady=2)
        self.font_options_map = {
            "ゴシック体 (MS Gothic)": "msgothic", "明朝体 (MS Mincho)": "msmincho",
            "メイリオ UI": "meiryo_ui", "游ゴシック UI": "yu_gothic_ui",
        }
        self.font_display_options = list(self.font_options_map.keys())
        self.font_family_var = StringVar(value=self.font_options_map["ゴシック体 (MS Gothic)"]) 
        self.font_dropdown_tk_var = StringVar(value="ゴシック体 (MS Gothic)") 
        self.font_option_menu = OptionMenu(text_image_frame, self.font_dropdown_tk_var, *self.font_display_options, command=self._on_font_dropdown_select)
        self.font_option_menu.grid(row=2, column=1, columnspan=2, sticky="ew", padx=5, pady=2)
        tk.Label(text_image_frame, text="文字濃度(%):").grid(row=3, column=0, sticky="w", pady=2)
        self.text_density_scale = Scale(text_image_frame, from_=0, to=100, resolution=1, orient=HORIZONTAL, showvalue=0, command=self._update_text_density)
        self.text_density_scale.set(100)
        self.text_density_scale.grid(row=3, column=1, padx=5, pady=2, sticky="ew")
        self.text_color_var = StringVar(value="#000000")
        tk.Button(text_image_frame, text="文字色選択", command=self._choose_text_color).grid(row=4, column=0, sticky="w", padx=2, pady=5)
        self.text_color_entry = tk.Entry(text_image_frame, textvariable=self.text_color_var, width=10)
        self.text_color_entry.grid(row=4, column=1, sticky="w", padx=5, pady=5)
        tk.Button(text_image_frame, text="選択範囲に追加/更新", command=self.add_text_as_image_to_selection).grid(row=4, column=2, pady=5)

    def _on_left_panel_mouse_wheel(self, event):
        x, y = self.root.winfo_pointerxy()
        try:
            widget_under_mouse = self.root.winfo_containing(x, y)
            current_widget = widget_under_mouse
            is_on_left_panel = False
            while current_widget:
                if current_widget == self.left_outer_frame: 
                    is_on_left_panel = True
                    break
                current_widget = current_widget.master
            if is_on_left_panel:
                delta = 0
                if platform.system() == "Windows": delta = int(-1*(event.delta/120))
                elif platform.system() == "Darwin": delta = int(-1*event.delta)
                else: delta = -1 if event.num == 4 else 1 if event.num == 5 else 0
                self.left_canvas_widget.yview_scroll(delta, "units")
        except: 
            pass

    def _setup_right_panel(self):
        right_outer_frame = tk.Frame(self.root, bd=2, relief=tk.SUNKEN)
        right_outer_frame.pack(side="right", fill="both", expand=True, padx=10, pady=10)
        image_preview_frame = tk.Frame(right_outer_frame, bd=1, relief=tk.SUNKEN)
        image_preview_frame.pack(fill="both", expand=True)
        self.v_scroll = tk.Scrollbar(image_preview_frame, orient="vertical")
        self.v_scroll.pack(side="right", fill="y")
        self.h_scroll = tk.Scrollbar(image_preview_frame, orient="horizontal")
        self.h_scroll.pack(side="bottom", fill="x")
        self.canvas = tk.Canvas(image_preview_frame, bg="lightgrey", yscrollcommand=self.v_scroll.set, xscrollcommand=self.h_scroll.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.v_scroll.config(command=self.canvas.yview)
        self.h_scroll.config(command=self.canvas.xview)

    def _bind_events(self):
        self.canvas.bind("<ButtonPress-1>", self.on_canvas_button_press)
        self.canvas.bind("<B1-Motion>", self.on_canvas_move_press)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_button_release)
        self.canvas.bind("<ButtonPress-3>", self.on_canvas_button_press) 
        self.canvas.bind("<B3-Motion>", self.on_canvas_move_press) 
        self.canvas.bind("<ButtonRelease-3>", self.on_canvas_button_release) 
        self.canvas.bind("<MouseWheel>", self._on_mouse_wheel)
        self.canvas.bind("<Button-4>", self._on_mouse_wheel)
        self.canvas.bind("<Button-5>", self._on_mouse_wheel)
        self.root.bind("<Control-s>", self._save_pdf_key_bind)
        self.root.bind("<Command-s>", self._save_pdf_key_bind)
        self.root.bind("<Control-z>", lambda event: self.undo_action())
        self.root.bind("<Command-z>", lambda event: self.undo_action()) 

    def _on_dropdown_select(self, selected_display_name):
        internal_value = self.display_to_value_map[selected_display_name]
        self.draw_mode_var.set(internal_value)
        self._on_mode_change()

    def _on_key_press(self, event):
        # この関数は、数字キーショートカットが削除されたため、実際には呼び出されません。
        # 将来的に別のキーバインドを追加する際に使用される可能性があります。
        try:
            key_num = int(event.char)
            if 1 <= key_num <= len(self.modes_list):
                selected_mode_value = self.modes_list[key_num - 1][1]
                selected_mode_display = self.modes_list[key_num - 1][0]
                self.draw_mode_var.set(selected_mode_value)
                self.dropdown_tk_var.set(selected_mode_display) 
                self._on_mode_change()
        except ValueError: pass

    def _on_mode_change(self):
        self._update_drawing_settings_state()
        if self.selected_ann: self.deselect_all_annotations()
        if self.draw_mode_var.get() == "insert_image": 
            self.canvas.config(cursor="crosshair")
        else:
            self.canvas.config(cursor="")

    def _update_drawing_settings_state(self):
        current_mode = self.draw_mode_var.get()
        is_drawing_mode = current_mode.startswith("draw_") 
        # 'textbox' モードの時も描画設定を有効にする
        is_drawing_mode_or_textbox = is_drawing_mode or (current_mode == "textbox") 
        if current_mode == "insert_image": 
            is_drawing_mode_or_textbox = False
        for child in self.drawing_settings_frame.winfo_children():
            if isinstance(child, (tk.Button, tk.Entry, Scale)):
                 child.config(state=tk.NORMAL if is_drawing_mode_or_textbox else tk.DISABLED)

    def _on_font_dropdown_select(self, selected_display_name): 
        self.font_family_var.set(self.font_options_map[selected_display_name])

    def _choose_line_color(self): 
        color_code = askcolor(title="線の色を選択", initialcolor=self.line_color_var.get())
        if color_code[1]: self.line_color_var.set(color_code[1])
            
    def update_font_size_label(self, value): self.font_size_label.config(text=f"{value}pt") 

    def _update_text_density(self, value_str): 
        density = int(value_str)
        gray_value = int(255 * (100 - density) / 100)
        self.text_color_var.set(f'#{gray_value:02x}{gray_value:02x}{gray_value:02x}')

    def _choose_text_color(self): 
        color_code = askcolor(title="文字色を選択", initialcolor=self.text_color_var.get())
        if color_code[1]:
            self.text_color_var.set(color_code[1])
            self.text_density_scale.set(100)

    def _get_font(self, font_size, font_family="gothic"): 
        font_key = (font_size, font_family, platform.system())
        if font_key in self.font_cache: return self.font_cache[font_key]
        font_path = None
        font_paths = {
            "Windows": {"msgothic": ["C:/Windows/Fonts/msgothic.ttc", "arial.ttf"], "msmincho": ["C:/Windows/Fonts/msmincho.ttc", "arial.ttf"], "meiryo_ui": ["C:/Windows/Fonts/meiryo.ttc", "arial.ttf"], "yu_gothic_ui": ["C:/Windows/Fonts/YuGothM.ttc", "C:/Windows/Fonts/Yu Gothic UI Regular.ttf", "arial.ttf"], "gothic": ["C:/Windows/Fonts/meiryo.ttc", "arial.ttf"], "mincho": ["C:/Windows/Fonts/YuMincho.ttc", "arial.ttf"]},
            "Darwin": {"gothic": ["/System/Library/Fonts/ヒラギノ角ゴシック W4.ttc", "Arial Unicode.ttf"], "mincho": ["/System/Library/Fonts/ヒラギノ明朝 ProN W3.ttc", "Arial Unicode.ttf"], "msgothic": ["Arial Unicode.ttf"], "msmincho": ["Arial Unicode.ttf"], "meiryo_ui": ["Arial Unicode.ttf"], "yu_gothic_ui": ["Arial Unicode.ttf"]},
            "Linux": {"gothic": ["NotoSansCJK-Regular.ttc", "ipag.ttf", "DejaVuSans.ttf"], "mincho": ["NotoSerifCJK-Regular.ttc", "ipam.ttf", "DejaVuSans.ttf"], "msgothic": ["DejaVuSans.ttf"], "msmincho": ["DejaVuSans.ttf"], "meiryo_ui": ["DejaVuSans.ttf"], "yu_gothic_ui": ["DejaVuSans.ttf"]}
        }
        candidate_fonts = font_paths.get(platform.system(), {}).get(font_family, [])
        for path_segment in candidate_fonts:
            if os.path.exists(path_segment): font_path = path_segment; break
        try:
            font = ImageFont.truetype(font_path, font_size) if font_path else ImageFont.load_default()
        except Exception as e:
            print(f"Font loading error for '{font_family}' at '{font_path}': {e}, using default.")
            font = ImageFont.load_default()
        self.font_cache[font_key] = font
        return font

    def _get_fitted_font_size(self, text_content, rect_width, rect_height, max_font_size=100, font_family="gothic"): 
        if not text_content or rect_width <= 0 or rect_height <= 0: return 0
        min_f, low, high, best_f = 1, 1, max_font_size, 1
        while low <= high:
            mid = (low + high) // 2
            if mid == 0: low = 1; continue
            font = self._get_font(mid, font_family)
            bbox = font.getbbox(text_content)
            if (bbox[2]-bbox[0]) <= rect_width and (bbox[3]-bbox[1]) <= rect_height:
                best_f = mid; low = mid + 1
            else: high = mid - 1
        return best_f
    
    def _save_state(self): 
        state = {'annotations': copy.deepcopy(self.annotations), 'current_page_index': self.current_page_index,
                 'selected_ann_coords': self.selected_ann['coords'] if self.selected_ann else None,
                 'page_rotations': {i: self.doc[i].rotation for i in range(len(self.doc))} if self.doc else {}} # ページ回転情報を保存
        self.undo_stack.append(state)
        if len(self.undo_stack) > self.max_undo_depth: self.undo_stack.pop(0)
        self.redo_stack.clear() 
        self._update_undo_redo_buttons()

    def _update_undo_redo_buttons(self): 
        # メニューバーの項目ではなく、左パネルのボタンの状態を更新
        if hasattr(self, 'undo_button') and self.undo_button:
            self.undo_button.config(state=tk.NORMAL if len(self.undo_stack) > 1 else tk.DISABLED)

    def undo_action(self): 
        if len(self.undo_stack) > 1:
            self._dirty_pages.add(self.current_page_index)
            self.undo_stack.pop() 
            restored_state = copy.deepcopy(self.undo_stack[-1])
            self.annotations = restored_state['annotations']
            self.current_page_index = restored_state['current_page_index']
            # ページ回転状態を復元
            if self.doc:
                for idx, rotation in restored_state.get('page_rotations', {}).items():
                    if idx < len(self.doc):
                        self.doc[idx].set_rotation(rotation)

            self.selected_ann = None
            if restored_state['selected_ann_coords']:
                for ann in self.annotations: 
                    if ann['coords'] == restored_state['selected_ann_coords'] and \
                       ann['page_idx'] == self.current_page_index:
                        self.selected_ann = ann; break
            self.page_entry.delete(0, tk.END); self.page_entry.insert(0, str(self.current_page_index))
            self._dirty_pages.add(self.current_page_index)
            self.show_page() 
            self._update_undo_redo_buttons()
        else: messagebox.showinfo("情報", "これ以上元に戻せる操作はありません。")

    def select_pdf(self): 
        path = filedialog.askopenfilename(filetypes=[("PDFファイル", "*.pdf")])
        if not path: return
        self.select_pdf_path(path) 

    def select_pdf_path(self, path): 
        try:
            if self.doc: self.doc.close()
            self.doc = fitz.open(path)
            self.pdf_path = path; self.current_page_index = 0
            self.filename_label.config(text=os.path.basename(path))
            self.page_entry.delete(0, tk.END); self.page_entry.insert(0, "0")
            self.annotations.clear(); self.canvas_item_to_ann.clear(); self.selected_ann = None
            self.zoom_scale.set(int(self.zoom_factor * 100))
            self.deselect_all_annotations()
            self._rendered_page_cache.clear(); self._page_cache_lru.clear(); self._dirty_pages.clear()
            self.show_page()
            self._save_state()
        except Exception as e:
            messagebox.showerror("エラー", f"PDF読み込み失敗: {e}")
            if self.doc: self.doc.close()
            self.doc = None; self.pdf_path = None
            self.filename_label.config(text="(未選択)")
            self.clear_canvas_and_reset_scroll()

    def set_zoom_factor_from_scale(self, value): 
        new_zoom = float(value) / 100.0
        if self.zoom_factor != new_zoom:
            self.zoom_factor = new_zoom
            self._rendered_page_cache.clear()
            self._page_cache_lru.clear()
            self._dirty_pages.clear() 
            self.show_page()

    def show_page(self): 
        if not self.doc: self.clear_canvas_and_reset_scroll(); return
        page_idx = self.current_page_index
        actual_zoom = max(0.01, self.zoom_factor)
        cache_key = (page_idx, actual_zoom, self.doc[page_idx].rotation) # 回転もキャッシュキーに含める
        needs_rerender = cache_key not in self._rendered_page_cache or page_idx in self._dirty_pages

        if needs_rerender:
            pix = self.doc[page_idx].get_pixmap(matrix=fitz.Matrix(actual_zoom, actual_zoom))
            mode = "RGB" if pix.alpha == 0 else "RGBA"
            current_pil_image = Image.frombytes(mode, [pix.width, pix.height], pix.samples)
            self._render_annotations_on_pil(current_pil_image, page_idx, actual_zoom)
            self._rendered_page_cache[cache_key] = current_pil_image
            if page_idx in self._dirty_pages: self._dirty_pages.remove(page_idx)
            if cache_key in self._page_cache_lru: self._page_cache_lru.remove(cache_key)
            self._page_cache_lru.append(cache_key)
            if len(self._page_cache_lru) > self.MAX_PAGE_CACHE_SIZE:
                oldest_key = self._page_cache_lru.pop(0)
                if oldest_key in self._rendered_page_cache: del self._rendered_page_cache[oldest_key]
            self.page_image_pil = current_pil_image 
        else:
            self.page_image_pil = self._rendered_page_cache[cache_key]
            if cache_key in self._page_cache_lru: self._page_cache_lru.remove(cache_key)
            self._page_cache_lru.append(cache_key)

        self.page_image_tk = ImageTk.PhotoImage(self.page_image_pil)
        self.canvas.delete("page_image")
        self.canvas.create_image(0,0,anchor="nw",image=self.page_image_tk, tags="page_image")
        self.canvas.config(scrollregion=(0,0,self.page_image_pil.width, self.page_image_pil.height))
        self.canvas.delete("annotation_group"); self.canvas_item_to_ann.clear()
        page_anns = [ann for ann in self.annotations if ann['page_idx'] == page_idx]
        for ann in page_anns: self._draw_annotation_bounding_box_on_canvas(ann, self.canvas_item_to_ann)
        self.update_page_info_label(); self.highlight_selected_annotation()

    def _render_annotations_on_pil(self, pil_image, page_idx, zoom): 
        draw = ImageDraw.Draw(pil_image)
        page_annotations = [ann for ann in self.annotations if ann['page_idx'] == page_idx]
        def get_render_order(ann): 
            type_order = {'redaction':0, 'mask':1, 'white_mask':1, 'image_object': 1.5, 'graphic_object':2, 'text_image':3}
            return type_order.get(ann.get('type'), 4)
        sorted_annotations = sorted(page_annotations, key=get_render_order)

        for ann in sorted_annotations:
            coords_pdf = ann['coords']
            x0_pil, y0_pil, x1_pil, y1_pil = [c * zoom for c in coords_pdf]
            pil_bbox_w, pil_bbox_h = x1_pil - x0_pil, y1_pil - y0_pil
            ann_type = ann.get('type')

            if ann_type == 'redaction': draw.rectangle((x0_pil, y0_pil, x1_pil, y1_pil), fill=self.redaction_color)
            elif ann_type == 'mask': draw.rectangle((x0_pil, y0_pil, x1_pil, y1_pil), fill=self.mask_color)
            elif ann_type == 'white_mask': draw.rectangle((x0_pil, y0_pil, x1_pil, y1_pil), fill=self.white_mask_color)
            elif ann_type == 'text_image' and ann.get('text_content', ''):
                text_content = ann.get('text_content', '')
                original_font_size = ann.get('font_size', 100)
                font_family = ann.get('font_family', 'gothic')
                text_color = ann.get('text_color', '#000000')
                fitted_font_size = self._get_fitted_font_size(text_content, pil_bbox_w, pil_bbox_h, int(original_font_size * zoom), font_family)
                if fitted_font_size > 0:
                    font = self._get_font(fitted_font_size, font_family)
                    ascent, descent = font.getmetrics()
                    text_draw_y = y0_pil + (pil_bbox_h - (ascent + descent)) / 2 
                    draw.text((x0_pil, text_draw_y), text_content, font=font, fill=text_color)
            elif ann_type == 'graphic_object' and pil_bbox_w > 0 and pil_bbox_h > 0:
                temp_graphic_pil = Image.new('RGBA', (int(math.ceil(pil_bbox_w)), int(math.ceil(pil_bbox_h))), (0,0,0,0))
                temp_draw = ImageDraw.Draw(temp_graphic_pil)
                shape_kind = ann.get('shape_kind')
                line_color = ann.get('line_color', '#000000')
                line_thickness = max(1, int(ann.get('line_thickness', 1) * zoom))
                if shape_kind == 'rectangle': temp_draw.rectangle([(0,0), (pil_bbox_w-1, pil_bbox_h-1)], outline=line_color, width=line_thickness)
                elif shape_kind == 'oval': temp_draw.ellipse([(0,0), (pil_bbox_w-1, pil_bbox_h-1)], outline=line_color, width=line_thickness)
                elif shape_kind == 'line':
                    spec_data = ann.get('shape_specific_data', {})
                    s, e = spec_data.get('start'), spec_data.get('end')
                    if s and e: temp_draw.line([((s[0]*zoom)-x0_pil, (s[1]*zoom)-y0_pil), ((e[0]*zoom)-x0_pil, (e[1]*zoom)-y0_pil)], fill=line_color, width=line_thickness)
                elif shape_kind == 'freehand':
                    points_pdf = ann.get('shape_specific_data', {}).get('points', [])
                    if len(points_pdf) > 1:
                        points_rel_pil = [((p[0]*zoom)-x0_pil, (p[1]*zoom)-y0_pil) for p in points_pdf]
                        temp_draw.line(points_rel_pil, fill=line_color, width=line_thickness, joint="curve")
                pil_image.paste(temp_graphic_pil, (int(x0_pil), int(y0_pil)), temp_graphic_pil)
            elif ann_type == 'image_object' and pil_bbox_w > 0 and pil_bbox_h > 0:
                image_data_bytes = ann.get('image_data')
                if image_data_bytes:
                    try:
                        img_to_paste_orig = Image.open(io.BytesIO(image_data_bytes))
                        img_to_paste_resized = img_to_paste_orig.copy()
                        img_to_paste_resized.thumbnail((int(pil_bbox_w), int(pil_bbox_h)), Image.LANCZOS)
                        paste_x, paste_y = int(x0_pil), int(y0_pil)
                        if img_to_paste_resized.mode != 'RGBA': img_to_paste_resized = img_to_paste_resized.convert('RGBA')
                        pil_image.paste(img_to_paste_resized, (paste_x, paste_y), img_to_paste_resized) 
                    except Exception as e: print(f"Error rendering pasted image: {e}")

    def _on_mouse_wheel(self, event): 
        delta = 0
        if platform.system() == "Windows": delta = int(-1*(event.delta/120))
        elif platform.system() == "Darwin": delta = int(-1*event.delta)
        else: delta = -1 if event.num == 4 else 1 if event.num == 5 else 0
        self.canvas.yview_scroll(delta, "units")

    def _draw_annotation_bounding_box_on_canvas(self, ann, item_map): 
        coords_pdf = ann['coords']
        coords_canvas = [c * self.zoom_factor for c in coords_pdf]
        outline_color, width, dash = self.default_text_box_outline_color, 1, ()
        ann_type = ann.get('type')
        
        # テキスト枠（text_box）の場合のデフォルト設定
        if ann_type == 'text_box': outline_color, width, dash = "blue", 2, () # テキスト枠は青色の実線、太さ2
        elif ann_type == 'text_image': outline_color, width = "green", 2
        elif ann_type == 'graphic_object': outline_color, width = "purple", 2
        elif ann_type == 'image_object': outline_color, width = "cyan", 2 
        elif ann_type in ['mask', 'white_mask', 'redaction']: outline_color, dash = "orange", (2,2)
        
        existing_item_id = ann['canvas_items'].get('rect')
        if existing_item_id and self.canvas.winfo_exists() and self.canvas.type(existing_item_id):
             self.canvas.coords(existing_item_id, *coords_canvas)
             self.canvas.itemconfig(existing_item_id, outline=outline_color, width=width, dash=dash)
        else:
            # 枠の太さを5に設定
            rect_id = self.canvas.create_rectangle(*coords_canvas, outline=outline_color, width=5, tags="annotation_group", dash=dash)
            ann['canvas_items']['rect'] = rect_id
            item_map[rect_id] = ann

    def go_to_page_from_entry(self): 
        if not self.doc: return messagebox.showerror("エラー", "PDF未選択")
        try:
            idx = int(self.page_entry.get())
            if not (0 <= idx < len(self.doc)): raise ValueError("ページ番号範囲外")
            if self.current_page_index != idx: 
                self.current_page_index = idx
                self.show_page()
        except ValueError as e: messagebox.showerror("エラー", f"正しいページ番号: {e}")

    def prev_page(self): 
        if self.doc and self.current_page_index > 0:
            self.current_page_index -= 1
            self.page_entry.delete(0, tk.END); self.page_entry.insert(0, str(self.current_page_index))
            self.show_page()

    def next_page(self): 
        if self.doc and self.current_page_index < len(self.doc) - 1:
            self.current_page_index += 1
            self.page_entry.delete(0, tk.END); self.page_entry.insert(0, str(self.current_page_index))
            self.show_page()

    def update_page_info_label(self): 
        if self.doc: self.page_info_label.config(text=f"{self.current_page_index + 1} / {len(self.doc)}")
        else: self.page_info_label.config(text="- / -")

    def on_canvas_button_press(self, event): 
        if not self.page_image_tk: return
        canvas_x, canvas_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        self.drag_start_x, self.drag_start_y = canvas_x, canvas_y
        self.drag_mode = 'none' # Reset drag mode

        # --- 既存のアノテーションを選択/移動/リサイズを試みる (すべてのモードで) ---
        items = self.canvas.find_overlapping(canvas_x-1, canvas_y-1, canvas_x+1, canvas_y+1)
        # 複数のアイテムが重なっている場合、最前面のアイテムを選択
        clicked_ann = next((self.canvas_item_to_ann[item_id] for item_id in reversed(items) if item_id in self.canvas_item_to_ann and self.canvas_item_to_ann[item_id]['page_idx'] == self.current_page_index), None)

        if clicked_ann:
            self.selected_ann = clicked_ann
            self.highlight_selected_annotation() # 新しく選択されたアノテーションをハイライト
            self._update_left_panel_for_selected_ann(clicked_ann) # 左パネルの設定を更新

            ann_coords_canvas = self.canvas.coords(self.selected_ann['canvas_items']['rect'])
            handle = self._get_resize_handle(canvas_x, canvas_y, ann_coords_canvas)

            if event.num == 1: # 左クリックでリサイズ
                if handle != 'none':
                    self.drag_mode = 'resize_' + handle
                    self.original_ann_coords_canvas = ann_coords_canvas
                    self.original_pdf_coords_for_resize = copy.deepcopy(self.selected_ann['coords'])
                    self.original_shape_specific_data_for_resize = copy.deepcopy(self.selected_ann.get('shape_specific_data')) if self.selected_ann.get('type') in ['graphic_object', 'image_object'] else None
                    return # 処理済み、終了
            elif event.num == 3: # 右クリックで移動
                self.drag_mode = 'move'
                self.original_ann_coords_canvas = ann_coords_canvas
                self.initial_pdf_coords_for_move = copy.deepcopy(self.selected_ann['coords'])
                return # 処理済み、終了

        # --- 既存のアノテーションが移動/リサイズされなかった場合、モード固有のアクションに進む ---
        current_mode = self.draw_mode_var.get()

        if current_mode == "insert_image":
            if event.num == 1:
                self._insert_image_at_click(canvas_x, canvas_y)
            return # 処理済み、終了

        if event.num == 1 and (current_mode.startswith("draw_") or current_mode == "textbox"):
            self.drag_mode = 'draw_shape'
            self.current_drawing_points_canvas = [(canvas_x, canvas_y)]
            shape = "draw_rectangle" if current_mode == "textbox" else current_mode
            
            # テキスト枠の場合、実線で太さを適用
            if shape=="draw_rectangle": 
                self.temp_canvas_item_id=self.canvas.create_rectangle(canvas_x,canvas_y,canvas_x,canvas_y,
                                                                      outline='blue', width=self.line_thickness_scale.get(), dash=())
            elif shape=="draw_oval": 
                self.temp_canvas_item_id=self.canvas.create_oval(canvas_x,canvas_y,canvas_x,canvas_y,
                                                                 outline=self.line_color_var.get(), width=self.line_thickness_scale.get(), dash=())
            elif shape=="draw_line": 
                self.temp_canvas_item_id=self.canvas.create_line(canvas_x,canvas_y,canvas_x,canvas_y,
                                                                 fill=self.line_color_var.get(), width=self.line_thickness_scale.get(), dash=())
            return # 処理済み、終了

        # 何もクリックされなかった、または「選択/操作」モードでハンドル外を左クリックした場合は選択解除
        self.deselect_all_annotations()


    def _get_resize_handle(self, mouse_x, mouse_y, ann_coords_canvas): 
        x0,y0,x1,y1 = ann_coords_canvas; t = self.RESIZE_HANDLE_SIZE
        if (x0-t<=mouse_x<=x0+t) and (y0-t<=mouse_y<=y0+t): return 'nw'
        if (x1-t<=mouse_x<=x1+t) and (y0-t<=mouse_y<=y0+t): return 'ne'
        if (x0-t<=mouse_x<=x0+t) and (y1-t<=mouse_y<=y1+t): return 'sw'
        if (x1-t<=mouse_x<=x1+t) and (y1-t<=mouse_y<=y1+t): return 'se'
        if (x0-t<=mouse_x<=x0+t) and (y0<=mouse_y<=y1): return 'w'
        if (x1-t<=mouse_x<=x1+t) and (y0<=mouse_y<=y1): return 'e'
        if (y0-t<=mouse_y<=y0+t) and (x0<=mouse_x<=x1): return 'n'
        if (y1-t<=mouse_y<=y1+t) and (x0<=mouse_x<=x1): return 's'
        return 'none'

    def on_canvas_move_press(self, event): 
        if self.drag_mode == 'none': return
        cur_x, cur_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        if self.drag_mode == 'draw_shape':
            shape = "draw_rectangle" if self.draw_mode_var.get() == "textbox" else self.draw_mode_var.get()
            if shape == "draw_freehand":
                self.current_drawing_points_canvas.append((cur_x,cur_y))
                if len(self.current_drawing_points_canvas)>1:
                    p1,p2 = self.current_drawing_points_canvas[-2], self.current_drawing_points_canvas[-1]
                    self.canvas.create_line(p1[0],p1[1],p2[0],p2[1],fill=self.line_color_var.get(),width=self.line_thickness_scale.get(),tags="temp_drawing_feedback")
            elif self.temp_canvas_item_id: self.canvas.coords(self.temp_canvas_item_id, self.drag_start_x,self.drag_start_y,cur_x,cur_y)
        elif self.drag_mode == 'move' and self.selected_ann and self.original_ann_coords_canvas:
            dx,dy = cur_x-self.drag_start_x, cur_y-self.drag_start_y
            x0,y0,x1,y1 = self.original_ann_coords_canvas
            self.canvas.coords(self.selected_ann['canvas_items']['rect'], x0+dx,y0+dy,x1+dx,y1+dy)
        elif self.drag_mode.startswith('resize_') and self.selected_ann and self.original_ann_coords_canvas:
            x0,y0,x1,y1 = self.original_ann_coords_canvas; nx0,ny0,nx1,ny1 = x0,y0,x1,y1
            h = self.drag_mode[7:]
            if 'w' in h: nx0=cur_x; 
            if 'e' in h: nx1=cur_x
            if 'n' in h: ny0=cur_y; 
            if 's' in h: ny1=cur_y
            self.canvas.coords(self.selected_ann['canvas_items']['rect'],min(nx0,nx1),min(ny0,ny1),max(nx0,nx1),max(ny0,ny1))

    def on_canvas_button_release(self, event): 
        if self.drag_mode == 'none': return
        end_x, end_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        current_draw_mode = self.draw_mode_var.get()

        if self.drag_mode == 'draw_shape':
            if self.temp_canvas_item_id: self.canvas.delete(self.temp_canvas_item_id); self.temp_canvas_item_id = None
            self.canvas.delete("temp_drawing_feedback")
            ann_type, shape_kind, shape_specific_data, coords_pdf = None, None, {}, None
            if current_draw_mode == "draw_freehand":
                if len(self.current_drawing_points_canvas) < 2: self.drag_mode = 'none'; self.current_drawing_points_canvas = []; return
                points_pdf = [(p[0]/self.zoom_factor, p[1]/self.zoom_factor) for p in self.current_drawing_points_canvas]
                min_x, min_y = min(p[0] for p in points_pdf), min(p[1] for p in points_pdf)
                max_x, max_y = max(p[0] for p in points_pdf), max(p[1] for p in points_pdf)
                coords_pdf = (min_x, min_y, max(min_x+1, max_x), max(min_y+1, max(min_y+1, max_y))) # 最小サイズ確保
                ann_type, shape_kind, shape_specific_data = 'graphic_object', 'freehand', {'points': points_pdf}
            else:
                x0_c, y0_c = min(self.drag_start_x,end_x), min(self.drag_start_y,end_y)
                x1_c, y1_c = max(self.drag_start_x,end_x), max(self.drag_start_y,end_y)
                if abs(x1_c-x0_c)<5 or abs(y1_c-y0_c)<5: self.drag_mode='none'; self.current_drawing_points_canvas=[]; return
                coords_pdf = tuple(c/self.zoom_factor for c in (x0_c,y0_c,x1_c,y1_c))
                
                if current_draw_mode == "textbox": 
                    ann_type = 'text_box'
                    shape_kind = 'rectangle'
                    # テキストボックスには線の色と太さをAnnotationとして保存
                    new_ann = {
                        'page_idx':self.current_page_index, 'coords':coords_pdf, 'type':ann_type, 
                        'canvas_items':{}, 'shape_kind':shape_kind, 
                        'line_color':self.line_color_var.get(), 'line_thickness':self.line_thickness_scale.get()
                    }
                else: # graphic_objectの場合
                    ann_type, shape_kind = 'graphic_object', current_draw_mode.split('_')[1]
                    if shape_kind == 'line': shape_specific_data = {'start': (self.drag_start_x/self.zoom_factor, self.drag_start_y/self.zoom_factor), 'end': (end_x/self.zoom_factor, end_y/self.zoom_factor)}
                    new_ann = {
                        'page_idx':self.current_page_index, 'coords':coords_pdf, 'type':ann_type, 
                        'canvas_items':{}, 'shape_kind':shape_kind, 
                        'line_color':self.line_color_var.get(), 'line_thickness':self.line_thickness_scale.get(), 
                        'shape_specific_data':shape_specific_data
                    }
            
            self.annotations.append(new_ann); self.selected_ann = new_ann
            self._dirty_pages.add(self.current_page_index)
            self._save_state(); self.show_page()
            if ann_type == 'text_box': # 新規テキスト枠作成後、テキスト入力欄にフォーカス
                self.text_to_add_as_image_entry.delete(0, tk.END)
                self.text_to_add_as_image_entry.focus_set()


        elif self.drag_mode == 'move' and self.selected_ann and self.initial_pdf_coords_for_move:
            current_canvas_coords = self.canvas.coords(self.selected_ann['canvas_items']['rect'])
            new_coords_pdf = tuple(c / self.zoom_factor for c in current_canvas_coords)
            dx_pdf = new_coords_pdf[0] - self.initial_pdf_coords_for_move[0]
            dy_pdf = new_coords_pdf[1] - self.initial_pdf_coords_for_move[1]
            if self.selected_ann.get('type') == 'graphic_object':
                spec_data = self.selected_ann.get('shape_specific_data', {})
                if self.selected_ann['shape_kind'] == 'line':
                    spec_data['start'] = (spec_data['start'][0] + dx_pdf, spec_data['start'][1] + dy_pdf)
                    spec_data['end'] = (spec_data['end'][0] + dx_pdf, spec_data['end'][1] + dy_pdf)
                elif self.selected_ann['shape_kind'] == 'freehand':
                    points = spec_data.get('points',[]); spec_data['points'] = [(p[0]+dx_pdf,p[1]+dy_pdf) for p in points] if points else []
            self.selected_ann['coords'] = new_coords_pdf
            self._dirty_pages.add(self.current_page_index); self._save_state(); self.show_page()

        elif self.drag_mode.startswith('resize_') and self.selected_ann and self.original_pdf_coords_for_resize:
            new_bbox_canvas = self.canvas.coords(self.selected_ann['canvas_items']['rect'])
            new_bbox_pdf = tuple(c / self.zoom_factor for c in new_bbox_canvas)
            old_bbox_pdf = self.original_pdf_coords_for_resize
            old_w, old_h = old_bbox_pdf[2]-old_bbox_pdf[0], old_bbox_pdf[3]-old_bbox_pdf[1]
            sx = (new_bbox_pdf[2]-new_bbox_pdf[0])/old_w if old_w!=0 else 1
            sy = (new_bbox_pdf[3]-new_bbox_pdf[1])/old_h if old_h!=0 else 1
            
            ann = self.selected_ann; ann['coords'] = new_bbox_pdf
            if ann.get('type') == 'graphic_object' and self.original_shape_specific_data_for_resize:
                orig_data, new_spec_data = self.original_shape_specific_data_for_resize, {}
                if ann['shape_kind'] == 'line':
                    s,e=orig_data['start'],orig_data['end']
                    new_spec_data['start']=(new_bbox_pdf[0]+(s[0]-old_bbox_pdf[0])*sx, new_bbox_pdf[1]+(s[1]-old_bbox_pdf[1])*sy)
                    new_spec_data['end']=(new_bbox_pdf[0]+(e[0]-old_bbox_pdf[0])*sx, new_bbox_pdf[1]+(e[1]-old_bbox_pdf[1])*sy)
                elif ann['shape_kind']=='freehand': new_spec_data['points']=[(new_bbox_pdf[0]+(p[0]-old_bbox_pdf[0])*sx, new_bbox_pdf[1]+(p[1]-old_bbox_pdf[1])*sy) for p in orig_data.get('points',[])]
                ann['shape_specific_data'] = new_spec_data
            elif ann.get('type') == 'image_object':
                pass
            self._dirty_pages.add(self.current_page_index); self._save_state(); self.show_page()
        
        self.drag_mode='none'; self.current_drawing_points_canvas=[]
        self.original_ann_coords_canvas=None; self.initial_pdf_coords_for_move=None
        self.original_pdf_coords_for_resize=None; self.original_shape_specific_data_for_resize=None

    def _update_left_panel_for_selected_ann(self, ann):
        """選択されたアノテーションのプロパティに基づいて左パネルのUIを更新するヘルパー"""
        ann_type = ann.get('type')
        # テキスト関連のUIをリセット
        self.text_to_add_as_image_entry.delete(0, tk.END)
        self.font_size_scale.set(100)
        self.font_dropdown_tk_var.set("ゴシック体 (MS Gothic)")
        self.font_family_var.set(self.font_options_map["ゴシック体 (MS Gothic)"])
        self.text_color_var.set("#000000")
        self.text_density_scale.set(100)
        # 描画設定関連のUIをリセット
        self.line_color_var.set("#000000")
        self.line_thickness_scale.set(2)

        if ann_type == 'text_image':
            self.text_to_add_as_image_entry.insert(0, ann.get('text_content', ''))
            self.font_size_scale.set(ann.get('font_size', 100))
            font_val = ann.get('font_family', 'msgothic')
            disp_name = next((d for d, v in self.font_options_map.items() if v == font_val), "ゴシック体 (MS Gothic)")
            self.font_dropdown_tk_var.set(disp_name)
            self.text_color_var.set(ann.get('text_color', '#000000'))
            # テキスト密度は直接設定しない（色から推測されるため）
            self.text_to_add_as_image_entry.focus_set()
        elif ann_type == 'graphic_object' or ann_type == 'text_box':
            self.line_color_var.set(ann.get('line_color', '#000000'))
            self.line_thickness_scale.set(ann.get('line_thickness', 2))
            # text_boxの場合、テキスト入力欄にフォーカスを当てる
            if ann_type == 'text_box':
                self.text_to_add_as_image_entry.focus_set()
        # For other types like 'image_object', 'mask', 'redaction', no specific text/drawing settings apply

    def highlight_selected_annotation(self): 
        if self.last_highlighted_item_id and self.last_highlighted_item_id in self.canvas_item_to_ann:
            ann = self.canvas_item_to_ann[self.last_highlighted_item_id]
            if ann:
                outline, width, dash = self.default_text_box_outline_color, 1, ()
                ann_type = ann.get('type')
                # ここもtext_boxの場合は実線で太さを考慮
                if ann_type == 'text_box': outline, width, dash = "blue", ann.get('line_thickness', 2), ()
                elif ann_type == 'text_image': outline, width = "green", 2
                elif ann_type == 'graphic_object': outline, width = "purple", 2
                elif ann_type == 'image_object': outline, width = "cyan", 2
                elif ann_type in ['mask','white_mask','redaction']: outline,dash="orange",(2,2)
                if self.canvas.winfo_exists() and self.canvas.type(self.last_highlighted_item_id):
                    try: self.canvas.itemconfig(self.last_highlighted_item_id, outline=outline, width=width, dash=dash)
                    except tk.TclError: pass
        self.last_highlighted_item_id = None
        if self.selected_ann and self.selected_ann['canvas_items'].get('rect'):
            item_id = self.selected_ann['canvas_items']['rect']
            if self.canvas.winfo_exists() and self.canvas.type(item_id):
                try: self.canvas.itemconfig(item_id, outline=self.selected_rect_color, width=3, dash=()); self.last_highlighted_item_id = item_id
                except tk.TclError: pass

    def delete_selected_annotation(self): 
        if self.selected_ann and messagebox.askyesno("確認", "選択されたオブジェクトを削除しますか？"):
            self._save_state(); self._dirty_pages.add(self.selected_ann['page_idx'])
            rect_id = self.selected_ann['canvas_items'].get('rect')
            if rect_id and self.canvas.winfo_exists() and self.canvas.type(rect_id): self.canvas.delete(rect_id)
            self.annotations.remove(self.selected_ann)
            if rect_id in self.canvas_item_to_ann: del self.canvas_item_to_ann[rect_id]
            self.selected_ann = None; self.show_page(); self.deselect_all_annotations()

    def delete_image_in_selected_rect(self): 
        if self.selected_ann and messagebox.askyesno("確認", "選択範囲をリダクションしますか？"):
            self._save_state(); self.selected_ann['type']='redaction'; self._dirty_pages.add(self.selected_ann['page_idx'])
            self.show_page(); self.highlight_selected_annotation()
        elif not self.selected_ann: messagebox.showinfo("情報", "範囲未選択")

    def mask_selected_area_black(self): 
        if self.selected_ann: self._save_state(); self.selected_ann['type']='mask'; self._dirty_pages.add(self.selected_ann['page_idx']); self.show_page(); self.highlight_selected_annotation()

    def mask_selected_area_white(self): 
        if self.selected_ann: self._save_state(); self.selected_ann['type']='white_mask'; self._dirty_pages.add(self.selected_ann['page_idx']); self.show_page(); self.highlight_selected_annotation()

    def deselect_all_annotations(self, keep_selection=False): 
        if not keep_selection: self.selected_ann = None
        self.highlight_selected_annotation()
        self.text_to_add_as_image_entry.delete(0,tk.END)
        self.font_size_scale.set(100)
        self.font_dropdown_tk_var.set("ゴシック体 (MS Gothic)")
        self.font_family_var.set(self.font_options_map["ゴシック体 (MS Gothic)"])
        self.text_color_var.set("#000000"); self.text_density_scale.set(100)
        # 線の色と太さをデフォルトに戻す
        self.line_color_var.set("#000000")
        self.line_thickness_scale.set(2)

    def add_text_as_image_to_selection(self): 
        if not self.selected_ann: return messagebox.showinfo("情報", "枠/図形を選択してください。")
        self._save_state()
        self.selected_ann.update({'type':'text_image', 'text_content':self.text_to_add_as_image_entry.get(),
                                  'font_size':self.font_size_scale.get(), 'font_family':self.font_family_var.get(),
                                  'text_color':self.text_color_var.get()})
        for key in ['shape_kind', 'shape_specific_data', 'image_data', 'line_color', 'line_thickness']: # 'line_color'と'line_thickness'も削除
            if key in self.selected_ann: del self.selected_ann[key]
        self._dirty_pages.add(self.selected_ann['page_idx']); self.show_page(); self.highlight_selected_annotation()

    def clear_pdf_selection(self): 
        if self.doc and messagebox.askyesno("確認", "PDF選択クリア？未保存の変更は失われます。"):
            self.doc.close(); self.doc=None; self.pdf_path=None
            self.filename_label.config(text="(未選択)")
            self.current_page_index=0; self.annotations.clear(); self.canvas_item_to_ann.clear()
            self.selected_ann=None; self.clear_canvas_and_reset_scroll(); self.update_page_info_label()
            self.undo_stack.clear(); self._save_state(); self._update_undo_redo_buttons()
            self._rendered_page_cache.clear(); self._page_cache_lru.clear(); self._dirty_pages.clear()

    def reload_pdf(self): 
        if self.pdf_path and messagebox.askyesno("確認", "PDF再読み込み？未保存の変更は失われます。"):
            path = self.pdf_path; self.clear_pdf_selection(); self.select_pdf_path(path)

    def clear_canvas_and_reset_scroll(self): 
        self.canvas.delete("all"); self.canvas.config(scrollregion=(0,0,0,0))
        self.page_image_pil = None; self.page_image_tk = None

    def _save_pdf_key_bind(self, event): self.save_pdf() 

    def save_pdf(self): 
        if not self.doc: return messagebox.showerror("エラー", "保存するPDFがありません。")
        output_path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDFファイル", "*.pdf")], initialfile=f"edited_{os.path.basename(self.pdf_path or 'document.pdf')}")
        if not output_path: return
        try:
            new_doc = fitz.open()
            for page_idx in range(len(self.doc)):
                original_page = self.doc[page_idx]
                new_page = new_doc.new_page(width=original_page.rect.width, height=original_page.rect.height)
                new_page.show_pdf_page(new_page.rect, self.doc, page_idx)
                page_annotations = [ann for ann in self.annotations if ann['page_idx'] == page_idx]
                def get_save_order(ann):
                    type_order = {'redaction':0, 'mask':1, 'white_mask':1, 'image_object':1.5, 'graphic_object':2, 'text_image':3}
                    return type_order.get(ann.get('type'), 4)
                sorted_annotations = sorted(page_annotations, key=get_save_order)

                for ann in sorted_annotations:
                    if ann.get('type') == 'redaction': new_page.add_redact_annot(fitz.Rect(ann['coords']))
                new_page.apply_redactions()

                for ann in sorted_annotations:
                    coords_pdf, ann_type = ann['coords'], ann.get('type')
                    rect_fitz = fitz.Rect(coords_pdf)
                    if ann_type == 'mask': new_page.draw_rect(rect_fitz, color=fitz.utils.getColor("black"), fill=fitz.utils.getColor("black"), overlay=True)
                    elif ann_type == 'white_mask': new_page.draw_rect(rect_fitz, color=fitz.utils.getColor("white"), fill=fitz.utils.getColor("white"), overlay=True)
                    elif ann_type == 'text_image' and ann.get('text_content',''):
                        text_content,font_size,font_family,text_color = ann.get('text_content',''),ann.get('font_size',100),ann.get('font_family','gothic'),ann.get('text_color','#000000')
                        fitted_font_size = self._get_fitted_font_size(text_content,rect_fitz.width,rect_fitz.height,font_size,font_family)
                        if fitted_font_size > 0:
                            font = self._get_font(fitted_font_size,font_family); bbox=font.getbbox(text_content)
                            img_w,img_h = bbox[2]-bbox[0],bbox[3]-bbox[1]
                            if img_w>0 and img_h>0:
                                text_pil=Image.new('RGBA',(img_w,img_h),(0,0,0,0)); ImageDraw.Draw(text_pil).text((-bbox[0],-bbox[1]),text_content,font=font,fill=text_color)
                                img_bytes=io.BytesIO(); text_pil.save(img_bytes,format='PNG'); new_page.insert_image(rect_fitz,stream=img_bytes.getvalue(),overlay=True)
                    elif ann_type == 'graphic_object' or ann_type == 'text_box': # text_boxもgraphic_objectとしてレンダリング
                        bbox_pdf = ann['coords']; bbox_w,bbox_h = bbox_pdf[2]-bbox_pdf[0],bbox_pdf[3]-bbox_pdf[1]
                        if bbox_w<=0 or bbox_h<=0: continue
                        temp_pil = Image.new('RGBA',(int(math.ceil(bbox_w)),int(math.ceil(bbox_h))),(0,0,0,0)); temp_draw=ImageDraw.Draw(temp_pil)
                        
                        shape_kind = ann.get('shape_kind')
                        color = ann.get('line_color','#000000') # テキスト枠も線の色と太さを持つ
                        thick = ann.get('line_thickness',1) # テキスト枠も線の色と太さを持つ
                        
                        if shape_kind=='rectangle': temp_draw.rectangle([(0,0),(bbox_w-1,bbox_h-1)],outline=color,width=thick)
                        elif shape_kind=='oval': temp_draw.ellipse([(0,0),(bbox_w-1,bbox_h-1)],outline=color,width=thick)
                        elif shape_kind=='line':
                            s,e=ann.get('shape_specific_data',{}).get('start'),ann.get('shape_specific_data',{}).get('end')
                            if s and e: temp_draw.line([(s[0]-bbox_pdf[0],s[1]-bbox_pdf[1]),(e[0]-bbox_pdf[0],e[1]-bbox_pdf[1])],fill=color,width=thick)
                        elif shape_kind=='freehand':
                            pts=ann.get('shape_specific_data',{}).get('points',[])
                            if len(pts)>1: temp_draw.line([(p[0]-bbox_pdf[0],p[1]-bbox_pdf[1]) for p in pts],fill=color,width=thick,joint="curve")
                        img_bytes=io.BytesIO(); temp_pil.save(img_bytes,format='PNG'); new_page.insert_image(fitz.Rect(bbox_pdf),stream=img_bytes.getvalue(),overlay=True)
                    elif ann_type == 'image_object':
                        image_data_bytes = ann.get('image_data')
                        if image_data_bytes:
                            try: new_page.insert_image(rect_fitz, stream=image_data_bytes, overlay=True)
                            except Exception as e: print(f"Error saving pasted image to PDF: {e}")
            new_doc.save(output_path); new_doc.close()
            messagebox.showinfo("保存完了", f"PDFを '{output_path}' に保存しました。")
        except Exception as e: messagebox.showerror("エラー", f"PDF保存失敗: {e}")

    def split_pdf(self): 
        if not self.doc: messagebox.showerror("エラー","PDF未選択"); return
        total_pages = len(self.doc)
        if total_pages == 0: messagebox.showinfo("情報","ページがありません"); return
        split_dialog = tk.Toplevel(self.root); split_dialog.title("PDF分割"); split_dialog.transient(self.root); split_dialog.grab_set()
        tk.Label(split_dialog, text=f"総ページ数: {total_pages} (0〜{total_pages-1})").grid(row=0,column=0,columnspan=2,padx=10,pady=5)
        tk.Label(split_dialog, text="開始ページ (0始):").grid(row=1,column=0,padx=10,pady=5); start_entry=tk.Entry(split_dialog,width=10); start_entry.grid(row=1,column=1,padx=10,pady=5); start_entry.insert(0,"0")
        tk.Label(split_dialog, text="終了ページ (0始):").grid(row=2,column=0,padx=10,pady=5); end_entry=tk.Entry(split_dialog,width=10); end_entry.grid(row=2,column=1,padx=10,pady=5); end_entry.insert(0,str(total_pages-1))
        def do_split():
            try:
                start,end = int(start_entry.get()), int(end_entry.get())
                if not (0<=start<total_pages and 0<=end<total_pages and start<=end): messagebox.showerror("エラー","無効なページ範囲",parent=split_dialog); return
                out_path = filedialog.asksaveasfilename(defaultextension=".pdf",initialfile=f"split_{os.path.basename(self.pdf_path or 'doc.pdf')}")
                if not out_path: split_dialog.destroy(); return
                new_pdf=fitz.open(); new_pdf.insert_pdf(self.doc,from_page=start,to_page=end); new_pdf.save(out_path); new_pdf.close()
                messagebox.showinfo("成功",f"'{out_path}' に保存",parent=split_dialog); split_dialog.destroy()
            except ValueError: messagebox.showerror("エラー","ページ番号は整数で",parent=split_dialog)
            except Exception as e: messagebox.showerror("エラー",f"分割エラー:\n{e}",parent=split_dialog)
        tk.Button(split_dialog,text="分割",command=do_split).grid(row=3,column=0,columnspan=2,pady=10)
        self.root.wait_window(split_dialog)

    def merge_pdfs(self): 
        if not self.doc: messagebox.showerror("エラー","結合ベースPDF未選択"); return
        merge_files = filedialog.askopenfilenames(title="結合するPDFを選択",filetypes=[("PDFファイル","*.pdf")])
        if not merge_files: return
        if messagebox.askyesno("結合方法","現在のPDFに結合しますか？\n'いいえ'で新規PDFとして結合"):
            base_doc = self.doc
            out_path = filedialog.asksaveasfilename(defaultextension=".pdf",initialfile=f"merged_{os.path.basename(self.pdf_path or 'doc.pdf')}")
            if not out_path: return
            try:
                for f_path in merge_files:
                    if f_path == self.pdf_path: messagebox.showinfo("情報",f"'{os.path.basename(f_path)}' は現在開いているPDFです。スキップ。",parent=self.root); continue
                    with fitz.open(f_path) as temp_doc: base_doc.insert_pdf(temp_doc)
                base_doc.save(out_path); messagebox.showinfo("成功",f"'{out_path}' に保存",parent=self.root)
                self.select_pdf_path(out_path) 
            except Exception as e: messagebox.showerror("エラー",f"結合エラー:\n{e}",parent=self.root)
        else:
            out_path = filedialog.asksaveasfilename(defaultextension=".pdf",initialfile="merged_all.pdf")
            if not out_path: return
            new_pdf = fitz.open()
            try:
                for f_path in merge_files:
                    with fitz.open(f_path) as temp_doc: new_pdf.insert_pdf(temp_doc)
                new_pdf.save(out_path); new_pdf.close(); messagebox.showinfo("成功",f"'{out_path}' に保存",parent=self.root)
                self.select_pdf_path(out_path)
            except Exception as e: messagebox.showerror("エラー",f"結合エラー:\n{e}",parent=self.root)
            finally:
                if new_pdf and not new_pdf.is_closed: new_pdf.close()

    def rotate_current_page(self):
        if not self.doc:
            messagebox.showerror("エラー", "PDFファイルが開かれていません。")
            return
        
        self._save_state() # 回転前の状態を保存
        current_page = self.doc[self.current_page_index]
        current_rotation = current_page.rotation
        new_rotation = (current_rotation + 90) % 360
        
        current_page.set_rotation(new_rotation)
        
        # ページが回転したため、キャッシュをクリアし、再描画を強制
        self._dirty_pages.add(self.current_page_index)
        self._rendered_page_cache.clear() # 全キャッシュをクリアしても良いが、対象ページだけでも十分
        self._page_cache_lru.clear() # LRUキャッシュもクリア
        
        self.show_page()
        # messagebox.showinfo("ページ回転", f"ページ {self.current_page_index + 1} を {new_rotation} 度に回転しました。") # この行を削除
        self._update_undo_redo_buttons() # Undo/Redoボタンの状態を更新

    def _insert_image_at_click(self, canvas_x, canvas_y):
        if not self.doc: messagebox.showerror("エラー", "まずPDFファイルを開いてください。"); return
        image_path = filedialog.askopenfilename(title="挿入する画像を選択", filetypes=[("画像ファイル", "*.png *.jpg *.jpeg *.gif *.bmp *.tiff"), ("すべてのファイル", "*.*")])
        if not image_path: return
        try:
            with open(image_path, "rb") as img_file: image_data_bytes = img_file.read()
            pil_img_temp = Image.open(io.BytesIO(image_data_bytes)); img_w_orig,img_h_orig=pil_img_temp.size; pil_img_temp.close()
            x0_pdf, y0_pdf = canvas_x/self.zoom_factor, canvas_y/self.zoom_factor
            disp_scale = 0.3; max_disp_w_pdf = (self.canvas.winfo_width()/self.zoom_factor)/2
            init_w_pdf = img_w_orig*disp_scale
            if init_w_pdf > max_disp_w_pdf: init_w_pdf = max_disp_w_pdf
            aspect = img_h_orig/img_w_orig if img_w_orig>0 else 1
            init_h_pdf = init_w_pdf*aspect
            x1_pdf, y1_pdf = x0_pdf+init_w_pdf, y0_pdf+init_h_pdf
            coords_pdf = (x0_pdf,y0_pdf,x1_pdf,y1_pdf)
            new_ann = {'page_idx':self.current_page_index, 'coords':coords_pdf, 'type':'image_object', 'image_data':image_data_bytes, 'canvas_items':{}}
            self.annotations.append(new_ann); self.selected_ann=new_ann
            self._dirty_pages.add(self.current_page_index); self._save_state(); self.show_page()
        except Exception as e: messagebox.showerror("画像挿入エラー", f"画像の読み込みまたは挿入中にエラーが発生しました:\n{e}")

if __name__ == "__main__":
    root = tk.Tk()
    app = PDFEditorApp(root)
    def on_closing():
        if app.doc: app.doc.close()
        root.destroy()
    root.protocol("WM_DELETE_WINDOW", on_closing)
    root.mainloop()

