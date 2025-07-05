import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, Scale, HORIZONTAL, StringVar, OptionMenu, BooleanVar, Checkbutton
from tkinter.colorchooser import askcolor
import fitz  # PyMuPDF (PDF処理ライブラリ)
from PIL import Image, ImageTk, ImageDraw, ImageFont # Pillow (画像処理ライブラリ)
import os # オペレーティングシステム機能 (ファイルパス操作など)
import platform # 実行環境のプラットフォーム情報
import io # インメモリバイナリI/O (画像データのバイト変換など)
import copy # オブジェクトのコピー操作 (undo/redo用)
import math # 数学関数 (楕円描画の計算など)

# TkDNDライブラリは使用しないため、関連するインポートとグローバル変数を削除

# === アプリケーションのメインクラス ===
class PDFEditorApp:
    """
    PDF編集アプリケーションのメインクラス。
    UIの構築、イベント処理、PDF操作機能全体を管理します。
    """
    def __init__(self, root):
        """
        PDFEditorAppのコンストラクタ。
        アプリケーションのウィンドウ設定、状態変数の初期化、UI要素の構築、イベントバインドを行います。

        Args:
            root (tk.Tk): Tkinterのルートウィンドウインスタンス。
        """
        self.root = root # Tkinterのルートウィンドウ
        root.title("PDF編集ツール") # ウィンドウのタイトルを設定
        root.geometry("1500x830") # ウィンドウの初期サイズを設定 (幅x高さ)

        # --- アプリケーションの状態変数 ---
        self.pdf_path = None # 現在開いているPDFファイルのフルパス
        self.doc = None # PyMuPDFのDocumentオブジェクト (現在開いているPDFドキュメント)
        self.current_page_index = 0 # 現在表示しているページのインデックス (0始まり)
        self.page_image_pil = None # 現在のページをレンダリングしたPillow Imageオブジェクト (アノテーション描画前)
        self.page_image_tk = None # Pillow ImageをTkinterで表示するためのPhotoImageオブジェクト (Canvas表示用)
        
        # アノテーション関連
        self.annotations = [] # 現在のPDFに追加された全てのアノテーションのリスト
                               # 各アノテーションは辞書形式で、ページインデックス、座標、タイプ、各種プロパティを保持
        self.selected_ann = None # 現在選択されているアノテーションオブジェクト (辞書)
        self.canvas_item_to_ann = {} # Canvas上のアイテムIDと対応するアノテーションオブジェクトをマッピングする辞書

        # ドラッグ操作関連
        self.drag_mode = 'none' # 現在のドラッグ操作モード ('none', 'draw_shape', 'move', 'resize_nw', 'resize_se', etc.)
        self.drag_start_x = None # ドラッグ開始時のCanvas X座標
        self.drag_start_y = None # ドラッグ開始時のCanvas Y座標
        self.original_ann_coords_canvas = None # ドラッグ開始時の選択アノテーションのCanvas座標 (リサイズ/移動の基準)
        self.initial_pdf_coords_for_move = None # 移動操作開始時の選択アノテーションのPDF座標
        self.current_drawing_points_canvas = [] # フリーハンド描画中の一時的な点のリスト (Canvas座標系)
        self.temp_canvas_item_id = None # 描画中の一時的なCanvasアイテムID (矩形、楕円、直線などのプレビュー用)

        # リサイズ操作関連
        self.original_pdf_coords_for_resize = None # リサイズ操作開始時の選択アノテーションのPDF座標
        self.original_shape_specific_data_for_resize = None # リサイズ操作開始時の図形固有データ (グラフィックオブジェクト用)

        # 表示・設定関連
        self.zoom_factor = 0.8 # ページの表示倍率 (例: 0.8 = 80%)
        self.selected_rect_color = "red" # 選択されたアノテーションのハイライト枠線の色
        self.default_text_box_outline_color = "blue" # テキストボックスのデフォルト枠線色
        self.mask_color = "black" # マスキング（黒塗り）の色
        self.white_mask_color = "white" # 白色マスキングの色
        self.redaction_color = "lightgrey" # リダクション（文字削除後）の背景色
        self.RESIZE_HANDLE_SIZE = 10 # リサイズハンドルの視覚的なサイズ (ピクセル単位)

        # フォント関連
        self.font_cache = {} # ロード済みのフォントオブジェクトをキャッシュするための辞書 (フォントサイズ、ファミリー、太字情報をキー)
        self.font_bold_var = BooleanVar(value=False) # テキスト太字化のON/OFFを保持するTkinter変数

        # Undo/Redo関連
        self.undo_stack = [] # 操作履歴を保存するスタック (元に戻す機能用)
        self.redo_stack = [] # やり直し操作履歴を保存するスタック (現在は未使用、将来的な拡張用)
        self.max_undo_depth = 20 # undoスタックの最大深度 (これを超えると古い履歴から削除される)

        # その他
        self.last_highlighted_item_id = None # 最後にハイライト表示されたCanvasアイテムのID (ハイライト解除用)
        self.copied_ann = None # コピーされたアノテーション情報を一時的に保持する変数

        # --- パフォーマンス改善のためのキャッシュ変数 ---
        self._rendered_page_cache = {} # レンダリング済みのページ画像 (PIL Image) をキャッシュするための辞書
                                      # キー: (ページインデックス, ズーム倍率, 回転角度)
        self._page_cache_lru = [] # LRU (Least Recently Used) アルゴリズムでキャッシュ管理するためのキーのリスト
        self.MAX_PAGE_CACHE_SIZE = 5 # ページキャッシュの最大サイズ (これを超えると古いキャッシュから削除)
        self._dirty_pages = set() # アノテーションの追加・変更などにより再レンダリングが必要なページのインデックスを保持するセット

        # --- モード選択リスト ---
        # (UI表示名, プログラム内部値) のタプルのリスト
        self.modes_list = [
            ("枠選択/操作", "select"),
            ("テキスト枠", "textbox"),
            ("矩形描画", "draw_rectangle"),
            ("楕円描画", "draw_oval"),
            ("直線描画", "draw_line"),
            ("フリーハンド描画", "draw_freehand"),
            ("画像挿入", "insert_image")
        ]
        # 表示名と内部値の相互マッピング用辞書を生成 (ルックアップ効率化のため)
        self.display_to_value_map = {display: value for display, value in self.modes_list}
        self.value_to_display_map = {value: display for display, value in self.modes_list}

        # --- UIのセットアップ ---
        # 各UIコンポーネントを初期化・配置
        self._setup_menu()          # メニューバー
        self._setup_left_panel()    # 左側コントロールパネル
        self._setup_right_panel()   # 右側PDFプレビューパネル
        self._bind_events()         # 各種イベントハンドラのバインド
        # ドラッグ＆ドロップ機能は削除されたため、_setup_dnd() の呼び出しも削除

        # --- 初期状態の保存とUI更新 ---
        self._save_state() # アプリケーション起動時の初期状態をundoスタックに保存
        self._update_undo_redo_buttons() # undo/redoボタンの有効/無効状態を更新

    def _setup_menu(self):
        """
        アプリケーションのメニューバーをセットアップします。
        「ファイル」メニューと「ヘルプ」メニューを作成し、各コマンドを割り当てます。
        """
        menubar = tk.Menu(self.root) # メインメニューバーオブジェクトを作成

        # --- ファイルメニュー ---
        file_menu = tk.Menu(menubar, tearoff=0) # tearoff=0 でメニューを分離不可にする
        menubar.add_cascade(label="ファイル", menu=file_menu) # "ファイル"カスケードメニューを追加
        # PDFを選択ボタンは左パネルに移動するため、ここから削除
        file_menu.add_command(label="PDFをクリア", command=self.clear_pdf_selection)
        file_menu.add_command(label="PDFを再読み込み", command=self.reload_pdf)
        file_menu.add_command(label="PDFを保存 (Ctrl+S)", command=self.save_pdf)
        file_menu.add_separator() # 区切り線
        file_menu.add_command(label="終了", command=self.root.quit) # アプリケーション終了

        # --- ヘルプメニュー ---
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="ヘルプ", menu=help_menu) # "ヘルプ"カスケードメニューを追加
        help_menu.add_command(label="バージョン情報", command=lambda: messagebox.showinfo("バージョン情報", "PDF編集ツール v1.4")) # バージョン情報を表示するダイアログ
        help_menu.add_command(label="操作方法", command=self._show_help_dialog) # 操作方法を表示するダイアログ

        self.root.config(menu=menubar) # 作成したメニューバーをウィンドウに設定

    def _show_help_dialog(self):
        """
        アプリケーションの基本的な操作方法を説明するヘルプダイアログを表示します。
        """
        help_text = """
PDF編集ツール 操作方法

1. ファイル操作 (メニューバー「ファイル」から):
   - PDFを選択/クリア/再読み込み/保存
   - 終了

2. PDFツール (左パネル):
   - PDFを選択: 新しいPDFファイルを開きます。
   - PDF分割: 選択したPDFの各ページを個別のPDFファイルとして保存します。
   - PDF結合: 複数のPDFを結合。
   - ページ回転: 現在のページを90度ずつ回転させます。
   - 元に戻す (Ctrl+Z / Cmd+Z): 直前の操作を取り消します。
   - 文字出力: 現在のページのテキストを右側のテキストプレビューに表示します。
   - 加工後プレビュー: 現在の編集内容を別ウィンドウでプレビューします。

3. ページと表示 (左パネル):
   - ページ移動、プレビュー倍率調整 (スライダーまたは Ctrl+マウスホイール)。

4. モード選択 (左パネル プルダウン):
   - 枠選択/操作: 図形を右クリックで選択、左クリックでリサイズ、右クリック長押しで移動。
   - テキスト枠: マスキングや文字追加のベースとなる矩形領域を作成。
   - 矩形/楕円/直線/フリーハンド描画: 各図形を描画。
   - 画像挿入: 画像ファイルを選択し、クリックした位置に挿入。

5. 描画設定 (左パネル、各描画モード時):
   - 線の色、線の太さ。

6. 図形と枠の操作 (左パネル):
   - 枠削除: 選択した枠/図形を削除。
   - 文字削除: 選択した枠/図形をリダクション（灰色塗り）する。
   - 黒色で塗りつぶし: 選択した枠/図形を黒色で塗りつぶす。
   - 白色で塗りつぶし: 選択した枠/図形を白色で塗りつぶす。
   - 枠選択解除: 現在選択されている枠/図形の選択を解除。
   - 選択範囲に追加/更新: 選択した枠/図形にテキストを画像として追加または更新。
   - コピー: 選択した枠/図形をコピーします。
   - ペースト: コピーした枠/図形を現在のページにペーストします。

7. テキストを画像として追加/編集 (左パネル):
   - 文字列、フォントサイズ、フォント、太字、文字濃度、文字色を設定して追加/更新。

ショートカット:
   - Ctrl+S (Cmd+S): 保存
   - Ctrl+Z (Cmd+Z): 元に戻す
   - Ctrl + マウスホイール: ズームイン/ズームアウト
        """
        messagebox.showinfo("操作方法", help_text)

    def _setup_left_panel(self):
        """
        アプリケーションの左側のコントロールパネルをセットアップします。
        ファイル情報、PDFツール、ページ操作、ズーム、モード選択、描画設定、枠操作、テキスト画像編集の各セクションが含まれます。
        パネル全体がスクロール可能になっています。
        """
        # 左パネルの外側フレーム (幅固定、高さ可変)
        self.left_outer_frame = tk.Frame(self.root, width=450)
        self.left_outer_frame.pack(side="left", fill="y", padx=10, pady=10)
        self.left_outer_frame.pack_propagate(False) # フレームサイズが子ウィジェットに影響されないようにする

        # スクロール可能なCanvasとScrollbarを左パネル内に作成
        self.left_canvas_widget = tk.Canvas(self.left_outer_frame, bg=self.root.cget('bg')) # 背景色をルートウィンドウに合わせる
        self.left_canvas_widget.pack(side="left", fill="both", expand=True)
        self.left_scrollbar = tk.Scrollbar(self.left_outer_frame, orient="vertical", command=self.left_canvas_widget.yview)
        self.left_scrollbar.pack(side="right", fill="y")
        self.left_canvas_widget.config(yscrollcommand=self.left_scrollbar.set)
        
        # Canvas内に実際にウィジェットを配置するための内部フレーム
        self.left_inner_frame = tk.Frame(self.left_canvas_widget, bg=self.root.cget('bg'))
        self.left_canvas_widget.create_window((0, 0), window=self.left_inner_frame, anchor="nw") # Canvasの左上に内部フレームを配置
        # 内部フレームのサイズ変更に応じてCanvasのスクロール領域を更新
        self.left_inner_frame.bind("<Configure>", lambda e: self.left_canvas_widget.configure(scrollregion=self.left_canvas_widget.bbox("all")))
        
        # 左パネルでのマウスホイールスクロールイベントをバインド (OS差異吸収)
        self.left_canvas_widget.bind("<MouseWheel>", self._on_left_panel_mouse_wheel) # Windows, macOS
        self.left_canvas_widget.bind("<Button-4>", self._on_left_panel_mouse_wheel) # Linux (ホイールアップ)
        self.left_canvas_widget.bind("<Button-5>", self._on_left_panel_mouse_wheel) # Linux (ホイールダウン)

        # --- ファイル名表示ラベル ---
        self.filename_label = tk.Label(self.left_inner_frame, text="(PDFファイル:未選択)", wraplength=430) # wraplengthで自動改行
        self.filename_label.pack(pady=5)

        # --- PDFツールセクション ---
        pdf_tools_frame = tk.LabelFrame(self.left_inner_frame, text="PDFツール", padx=10, pady=5)
        pdf_tools_frame.pack(fill="x", pady=5)
        
        # 「PDFを選択」ボタンをPDFツールセクションに追加
        tk.Button(pdf_tools_frame, text="PDFを選択", command=self.select_pdf, width=12).grid(row=0, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="PDF分割", command=self.split_pdf, width=12).grid(row=0, column=1, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="PDF結合", command=self.merge_pdfs, width=12).grid(row=1, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="ページ回転", command=self.rotate_current_page, width=12).grid(row=1, column=1, pady=2, padx=2, sticky="ew")
        self.undo_button = tk.Button(pdf_tools_frame, text="元に戻す (Ctrl+Z)", command=self.undo_action, state=tk.DISABLED, width=12)
        self.undo_button.grid(row=2, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="文字出力", command=self.extract_text_to_preview, width=12).grid(row=2, column=1, pady=2, padx=2, sticky="ew")
        tk.Button(pdf_tools_frame, text="加工後プレビュー", command=self.show_processed_preview, width=12).grid(row=3, column=0, columnspan=2, pady=2, padx=2, sticky="ew")


        # --- ページ操作 & ズームセクション ---
        page_zoom_container = tk.Frame(self.left_inner_frame) # ページ操作とズームを横並びにするためのコンテナ
        page_zoom_container.pack(fill="x", pady=5)
        
        page_frame = tk.LabelFrame(page_zoom_container, text="ページ操作", padx=10, pady=5)
        page_frame.pack(side="left", fill="x", expand=True, padx=(0,2)) # 左側に配置
        tk.Label(page_frame, text="ページ(0始):").grid(row=0, column=0, sticky="w")
        self.page_entry = tk.Entry(page_frame, width=4) # ページ番号入力欄
        self.page_entry.grid(row=0, column=1, padx=2)
        self.page_entry.insert(0, "0")
        tk.Button(page_frame, text="表示", command=self.go_to_page_from_entry, width=4).grid(row=0, column=2, padx=2)
        
        page_nav_frame = tk.Frame(page_frame) # 前へ/次へボタン用フレーム
        page_nav_frame.grid(row=1, column=0, columnspan=3, pady=2)
        tk.Button(page_nav_frame, text="<<前へ", command=self.prev_page).pack(side="left", padx=2)
        self.page_info_label = tk.Label(page_nav_frame, text="- / -") # "現在のページ / 総ページ数" 表示
        self.page_info_label.pack(side="left", padx=2)
        tk.Button(page_nav_frame, text="次へ>>", command=self.next_page).pack(side="left", padx=2)

        zoom_frame = tk.LabelFrame(page_zoom_container, text="倍率", padx=10, pady=5)
        zoom_frame.pack(side="right", fill="x", expand=True, padx=(2,0)) # 右側に配置
        # ズーム倍率を調整するスライダー (10%から800%まで)
        self.zoom_scale = Scale(zoom_frame, from_=10, to=800, resolution=10, orient=HORIZONTAL,
                                label="%", command=self.set_zoom_factor_from_scale)
        self.zoom_scale.set(int(self.zoom_factor * 100)) # 初期ズーム倍率を設定
        self.zoom_scale.pack(fill="x", expand=True, pady=0)
        
        # --- モード選択セクション ---
        mode_selection_frame = tk.LabelFrame(self.left_inner_frame, text="モード選択", padx=10, pady=5)
        mode_selection_frame.pack(fill="x", pady=5)
        self.draw_mode_var = StringVar(value="textbox") # 現在の描画モードを保持 (内部値)
        initial_display_name = self.value_to_display_map.get("textbox", self.modes_list[1][0])
        self.dropdown_tk_var = StringVar(value=initial_display_name) # プルダウン表示用のStringVar
        self.mode_option_menu = OptionMenu(mode_selection_frame, self.dropdown_tk_var, 
                                           *[m[0] for m in self.modes_list], command=self._on_dropdown_select) # モード選択プルダウン
        self.mode_option_menu.config(width=20)
        self.mode_option_menu.pack(fill="x", padx=2, pady=1)

        # --- 描画設定セクション ---
        self.drawing_settings_frame = tk.LabelFrame(self.left_inner_frame, text="描画設定", padx=10, pady=5)
        self.drawing_settings_frame.pack(fill="x", pady=5)
        tk.Label(self.drawing_settings_frame, text="線の色:").grid(row=0, column=0, sticky="w", pady=2)
        self.line_color_var = StringVar(value="#000000") # 線の色 (HEX)
        self.line_color_button = tk.Button(self.drawing_settings_frame, text="色選択", command=self._choose_line_color, width=8)
        self.line_color_button.grid(row=0, column=1, padx=2, pady=2)
        self.line_color_entry = tk.Entry(self.drawing_settings_frame, textvariable=self.line_color_var, width=10)
        self.line_color_entry.grid(row=0, column=2, padx=2, pady=2)
        tk.Label(self.drawing_settings_frame, text="線の太さ:").grid(row=0, column=3, sticky="w", pady=2)
        self.line_thickness_scale = Scale(self.drawing_settings_frame, from_=1, to=20, orient=HORIZONTAL, resolution=1, showvalue=True)
        self.line_thickness_scale.set(7) # 線の太さの初期値を7に変更
        self.line_thickness_scale.grid(row=0, column=4, padx=2, pady=2, sticky="ew")
        self._update_drawing_settings_state() # 初期状態でのUI有効/無効を設定

        # --- 枠/オブジェクト操作セクション ---
        edit_frame = tk.LabelFrame(self.left_inner_frame, text="枠/オブジェクト操作", padx=10, pady=5)
        edit_frame.pack(fill="x", pady=5)
        edit_button_grid_frame = tk.Frame(edit_frame) # ボタン配置用の内部フレーム
        edit_button_grid_frame.pack(pady=5, fill="x")
        tk.Button(edit_button_grid_frame, text="枠削除", command=self.delete_selected_annotation, width=12).grid(row=0, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="文字削除", command=self.delete_image_in_selected_rect, width=12).grid(row=0, column=1, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="黒色で塗りつぶし", command=self.mask_selected_area_black, width=12).grid(row=0, column=2, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="白色で塗りつぶし", command=self.mask_selected_area_white, width=12).grid(row=0, column=3, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="枠選択解除", command=self.deselect_all_annotations, width=25).grid(row=1, column=0, columnspan=4, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="コピー", command=self.copy_selected_annotation, width=12).grid(row=2, column=0, pady=2, padx=2, sticky="ew")
        tk.Button(edit_button_grid_frame, text="ペースト", command=self.paste_annotation, width=12).grid(row=2, column=1, pady=2, padx=2, sticky="ew")
        
        # --- テキストを画像として追加/編集セクション ---
        text_image_frame = tk.LabelFrame(self.left_inner_frame, text="テキストを画像として追加/編集", padx=10, pady=5)
        text_image_frame.pack(fill="x", pady=5)
        tk.Label(text_image_frame, text="文字列:").grid(row=0, column=0, sticky="w", pady=2)
        self.text_to_add_as_image_entry = tk.Entry(text_image_frame, width=40) # 入力文字列
        self.text_to_add_as_image_entry.grid(row=0, column=1, columnspan=3, padx=5, pady=2) # columnspan を3に変更
        
        tk.Label(text_image_frame, text="フォントサイズ:").grid(row=1, column=0, sticky="w", pady=2)
        self.font_size_scale = Scale(text_image_frame, from_=10, to=100, resolution=1, orient=HORIZONTAL, label="", command=self.update_font_size_label)
        self.font_size_scale.set(100)
        self.font_size_scale.grid(row=1, column=1, padx=5, pady=2, sticky="ew")
        self.font_size_label = tk.Label(text_image_frame, text="100pt")
        self.font_size_label.grid(row=1, column=2, sticky="w", padx=2)
        
        tk.Label(text_image_frame, text="フォント:").grid(row=2, column=0, sticky="w", pady=2)
        self.font_options_map = { # フォント表示名と内部名のマッピング
            "ゴシック体 (MS Gothic)": "msgothic", "明朝体 (MS Mincho)": "msmincho",
            "メイリオ UI": "meiryo_ui", "游ゴシック UI": "yu_gothic_ui",
        }
        self.font_display_options = list(self.font_options_map.keys()) # プルダウン表示用リスト
        self.font_family_var = StringVar(value=self.font_options_map["ゴシック体 (MS Gothic)"]) # 選択されたフォントファミリー (内部名)
        self.font_dropdown_tk_var = StringVar(value="ゴシック体 (MS Gothic)") # プルダウン表示用
        self.font_option_menu = OptionMenu(text_image_frame, self.font_dropdown_tk_var, *self.font_display_options, command=self._on_font_dropdown_select)
        self.font_option_menu.grid(row=2, column=1, columnspan=2, sticky="ew", padx=5, pady=2)
        
        # 太字チェックボックスを追加
        self.bold_checkbutton = Checkbutton(text_image_frame, text="太字", variable=self.font_bold_var)
        self.bold_checkbutton.grid(row=2, column=3, sticky="w", padx=5, pady=2)


        tk.Label(text_image_frame, text="文字濃度(%):").grid(row=3, column=0, sticky="w", pady=2)
        self.text_density_scale = Scale(text_image_frame, from_=0, to=100, resolution=1, orient=HORIZONTAL, showvalue=0, command=self._update_text_density)
        self.text_density_scale.set(100)
        self.text_density_scale.grid(row=3, column=1, padx=5, pady=2, sticky="ew")
        
        self.text_color_var = StringVar(value="#000000") # 文字色 (HEX)
        tk.Button(text_image_frame, text="文字色選択", command=self._choose_text_color).grid(row=4, column=0, sticky="w", padx=2, pady=5)
        self.text_color_entry = tk.Entry(text_image_frame, textvariable=self.text_color_var, width=10)
        self.text_color_entry.grid(row=4, column=1, sticky="w", padx=5, pady=5)
        tk.Button(text_image_frame, text="選択範囲に追加/更新", command=self.add_text_as_image_to_selection).grid(row=4, column=2, columnspan=2, pady=5, sticky="ew") # columnspan を2に変更

    def _on_left_panel_mouse_wheel(self, event):
        """
        左パネル上でのマウスホイールイベントを処理し、パネル内容をスクロールします。
        Windows, macOS, Linuxの各プラットフォームでのホイールイベントの違いを吸収します。

        Args:
            event: マウスホイールイベントオブジェクト。
        """
        # マウスカーソル下のウィジェットが左パネル内にあるかを確認
        # (より堅牢な方法として、イベント発生ウィジェットがleft_canvas_widgetの子孫であるかを確認する方が良い場合もある)
        x, y = self.root.winfo_pointerxy() # スクリーン上のマウスカーソル座標
        try:
            widget_under_mouse = self.root.winfo_containing(x, y) # マウス直下のウィジェット
            current_widget = widget_under_mouse
            is_on_left_panel = False
            while current_widget: # 親ウィジェットを辿って left_outer_frame に到達するか確認
                if current_widget == self.left_outer_frame: 
                    is_on_left_panel = True
                    break
                current_widget = current_widget.master
            
            if is_on_left_panel: # 左パネル上でのみスクロールを実行
                delta = 0
                if platform.system() == "Windows":
                    delta = int(-1*(event.delta/120)) # Windows: event.delta は通常120の倍数
                elif platform.system() == "Darwin": # macOS
                    delta = int(-1*event.delta)      # macOS: event.delta はピクセル単位に近い値
                else: # Linux (X11)
                    # Button-4 (ホイールアップ), Button-5 (ホイールダウン)
                    delta = -1 if event.num == 4 else 1 if event.num == 5 else 0
                self.left_canvas_widget.yview_scroll(delta, "units") # Canvasをスクロール
        except Exception: 
            # ウィジェットが既に破棄されている場合などにエラーが発生する可能性があるため、念のため捕捉
            pass

    def _setup_right_panel(self):
        """
        アプリケーションの右側のPDFプレビューパネルをセットアップします。
        PDFページ画像を表示するCanvasと、抽出テキストを表示するTextウィジェット、およびそれぞれのスクロールバーが含まれます。
        """
        # 右パネルの外側フレーム (枠線付き)
        right_outer_frame = tk.Frame(self.root, bd=2, relief=tk.SUNKEN)
        right_outer_frame.pack(side="right", fill="both", expand=True, padx=10, pady=10)

        # 画像プレビューとテキストプレビューを横に並べるためのコンテナフレーム
        preview_container_frame = tk.Frame(right_outer_frame)
        preview_container_frame.pack(fill="both", expand=True)

        # --- 画像プレビューフレーム (左側) ---
        image_preview_frame = tk.Frame(preview_container_frame, bd=1, relief=tk.SUNKEN)
        image_preview_frame.pack(side="left", fill="both", expand=True, padx=(0, 5)) # 右に少しマージン

        self.v_scroll = tk.Scrollbar(image_preview_frame, orient="vertical") # 垂直スクロールバー
        self.v_scroll.pack(side="right", fill="y")
        self.h_scroll = tk.Scrollbar(image_preview_frame, orient="horizontal") # 水平スクロールバー
        self.h_scroll.pack(side="bottom", fill="x")
        
        # PDFページ画像とアノテーションを表示するメインCanvas
        self.canvas = tk.Canvas(image_preview_frame, bg="lightgrey", 
                                yscrollcommand=self.v_scroll.set, xscrollcommand=self.h_scroll.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.v_scroll.config(command=self.canvas.yview) # スクロールバーとCanvasを連携
        self.h_scroll.config(command=self.canvas.xview)

        # --- テキストプレビューフレーム (右側) ---
        self.text_preview_frame = tk.Frame(preview_container_frame, bd=1, relief=tk.SUNKEN)
        self.text_preview_frame.pack(side="right", fill="both", expand=True, padx=(5, 0)) # 左に少しマージン

        self.text_output = tk.Text(self.text_preview_frame, wrap="word", state="disabled", width=5) # テキスト表示ウィジェット (初期は読み取り専用)
        self.text_output.pack(side="left", fill="both", expand=True)
        text_v_scroll = tk.Scrollbar(self.text_preview_frame, orient="vertical", command=self.text_output.yview) # テキスト用垂直スクロールバー
        text_v_scroll.pack(side="right", fill="y")
        self.text_output.config(yscrollcommand=text_v_scroll.set) # スクロールバーとTextウィジェットを連携

    def _bind_events(self):
        """
        Canvasおよびルートウィンドウの主要なイベントハンドラをバインドします。
        マウス操作 (クリック、ドラッグ、ホイール) やキーボードショートカットが含まれます。
        """
        # --- Canvasのマウスイベント ---
        # 左クリック
        self.canvas.bind("<ButtonPress-1>", self.on_canvas_button_press)   # ボタン押下時
        self.canvas.bind("<B1-Motion>", self.on_canvas_move_press)         # ドラッグ時
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_button_release) # ボタン離上時
        # 右クリック (主に選択と移動用)
        self.canvas.bind("<ButtonPress-3>", self.on_right_click_select)    # ボタン押下時
        self.canvas.bind("<B3-Motion>", self.on_canvas_move_press)         # ドラッグ時 (移動用)
        self.canvas.bind("<ButtonRelease-3>", self.on_canvas_button_release) # ボタン離上時
        
        # Canvasのマウスホイールイベント (PDFプレビューのスクロール)
        self.canvas.bind("<MouseWheel>", self._on_mouse_wheel) # Windows/macOS (通常スクロール)
        self.canvas.bind("<Button-4>", self._on_mouse_wheel)   # Linux (ホイールアップ、通常スクロール)
        self.canvas.bind("<Button-5>", self._on_mouse_wheel)   # Linux (ホイールダウン、通常スクロール)

        # Ctrl + マウスホイールでのズームイベント
        self.canvas.bind("<Control-MouseWheel>", self._on_ctrl_mouse_wheel) # Windows/macOS
        self.canvas.bind("<Control-Button-4>", self._on_ctrl_mouse_wheel)   # Linux (Ctrl + ホイールアップ)
        self.canvas.bind("<Control-Button-5>", self._on_ctrl_mouse_wheel)   # Linux (Ctrl + ホイールダウン)
        
        # --- ルートウィンドウのキーボードショートカット ---
        self.root.bind("<Control-s>", self._save_pdf_key_bind) # Ctrl+S (Windows/Linux)
        self.root.bind("<Command-s>", self._save_pdf_key_bind) # Command+S (macOS) - PDF保存
        self.root.bind("<Control-z>", lambda event: self.undo_action()) # Ctrl+Z - 元に戻す
        self.root.bind("<Command-z>", lambda event: self.undo_action()) # Command+Z (macOS) - 元に戻す

    def _setup_dnd(self):
        """
        Tkinterアプリケーション全体でドラッグ＆ドロップ機能をセットアップします。
        このバージョンではTkDNDライブラリへの依存を削除したため、このメソッドは空です。
        """
        # TkDNDライブラリへの依存を削除したため、DND機能は提供しません。
        pass

    # ドラッグ＆ドロップ関連のイベントハンドラも削除
    # def _on_dnd_enter(self, event): ...
    # def _on_dnd_drag(self, event): ...
    # def _on_dnd_leave(self, event): ...
    # def _on_dnd_drop(self, event): ...


    def _on_ctrl_mouse_wheel(self, event):
        """
        メインCanvas上でCtrlキーを押しながらマウスホイールを操作したときのイベントハンドラ。
        ズーム倍率を調整します。
        """
        if not self.doc: # PDFが開かれていない場合は何もしない
            return

        delta = 0
        if platform.system() == "Windows": # Windows
            delta = event.delta // 120 # 通常120の倍数で変化
        elif platform.system() == "Darwin": # macOS
            delta = event.delta # 連続的な値で変化 (1か-1に近いことが多い)
        else: # Linux (X11)
            if event.num == 4: # ホイールアップ
                delta = 1
            elif event.num == 5: # ホイールダウン
                delta = -1
        
        if delta == 0: # スクロール量が不明、または極小の場合は処理しない
            return

        current_zoom_percentage = self.zoom_scale.get() # 現在のスライダーの値 (10-800)
        
        # ズームステップ (パーセント単位)
        zoom_step_percentage = 10 

        if delta > 0: # ホイールアップ (拡大)
            new_zoom_percentage = min(current_zoom_percentage + zoom_step_percentage, 800)
        else: # ホイールダウン (縮小)
            new_zoom_percentage = max(current_zoom_percentage - zoom_step_percentage, 10)
        
        if new_zoom_percentage != current_zoom_percentage:
            self.zoom_scale.set(new_zoom_percentage) # スケールウィジェットの値を更新
            # スケールのcommand (self.set_zoom_factor_from_scale) が自動的に呼び出され、
            # self.zoom_factor の更新とページの再表示が行われる。

    def _on_dropdown_select(self, selected_display_name):
        """
        モード選択プルダウンメニューで項目が選択されたときに呼び出されます。
        選択された表示名に対応する内部モード値を設定し、モード変更時の処理を実行します。

        Args:
            selected_display_name (str): プルダウンで選択された表示名。
        """
        internal_value = self.display_to_value_map[selected_display_name] # 表示名から内部値を取得
        self.draw_mode_var.set(internal_value) # 描画モードのStringVarを更新
        self._on_mode_change() # モード変更に伴う共通処理を実行

    def _on_key_press(self, event):
        """
        キーボード押下イベントを処理します。(現在は直接使用されていません)
        将来的にモード切り替えなどに数字キーショートカットを割り当てる場合などに使用できます。

        Args:
            event: キーボードイベントオブジェクト。
        """
        try:
            key_num = int(event.char) # 押されたキーが数字か試みる
            if 1 <= key_num <= len(self.modes_list): # モードリストの範囲内か
                selected_mode_value = self.modes_list[key_num - 1][1] # 対応する内部値
                selected_mode_display = self.modes_list[key_num - 1][0] # 対応する表示名
                self.draw_mode_var.set(selected_mode_value)
                self.dropdown_tk_var.set(selected_mode_display) # プルダウンの表示も更新
                self._on_mode_change()
        except ValueError: # 数字以外のキーが押された場合は何もしない
            pass

    def _on_mode_change(self):
        """
        描画モードが変更されたときに呼び出される共通処理です。
        描画設定UIの有効/無効状態を更新し、選択中のアノテーションがあれば解除します。
        また、モードに応じてCanvasのカーソル形状を変更します。
        """
        self._update_drawing_settings_state() # 描画設定UIの有効/無効を更新
        if self.selected_ann: # モード変更時は、既存の選択を解除
            self.deselect_all_annotations()
        
        # カーソル形状をモードに応じて変更
        if self.draw_mode_var.get() == "insert_image": 
            self.canvas.config(cursor="crosshair") # 画像挿入モードでは十字カーソル
        else:
            self.canvas.config(cursor="") # その他のモードではデフォルトカーソル (標準矢印)

    def _update_drawing_settings_state(self):
        """
        現在の描画モードに基づいて、左パネルの「描画設定」UI要素（線の色、線の太さ）の
        有効/無効状態を更新します。
        描画系モード（矩形、楕円、直線、フリーハンド）、テキストボックスモード、画像挿入モードの場合に有効になります。
        """
        current_mode = self.draw_mode_var.get()
        is_drawing_related_mode = current_mode.startswith("draw_") or \
                                  current_mode == "textbox" or \
                                  current_mode == "insert_image"
        
        new_state = tk.NORMAL if is_drawing_related_mode else tk.DISABLED
        
        # 描画設定フレーム内の関連ウィジェットの状態を一括変更
        for child in self.drawing_settings_frame.winfo_children():
            if isinstance(child, (tk.Button, tk.Entry, Scale)): # 対象ウィジェットタイプ
                 child.config(state=new_state)

    def _on_font_dropdown_select(self, selected_display_name): 
        """
        フォント選択プルダウンメニューで項目が選択されたときに呼び出されます。
        選択された表示名に対応する内部フォントファミリー値を設定します。

        Args:
            selected_display_name (str): プルダウンで選択されたフォントの表示名。
        """
        self.font_family_var.set(self.font_options_map[selected_display_name])

    def _choose_line_color(self): 
        """
        「線の色選択」ボタンが押されたときに呼び出されます。
        カラーピッカーダイアログを表示し、選択された色を線の色として設定します。
        """
        color_code = askcolor(title="線の色を選択", initialcolor=self.line_color_var.get())
        if color_code[1]: # 色が選択された場合 (color_code[1] は選択された色のHEX文字列)
            self.line_color_var.set(color_code[1])
            
    def update_font_size_label(self, value): 
        """
        フォントサイズスライダーの値が変更されたときに、フォントサイズの表示ラベルを更新します。

        Args:
            value (str): スライダーから渡される現在の値 (文字列型)。
        """
        self.font_size_label.config(text=f"{value}pt")

    def _update_text_density(self, value_str): 
        """
        文字濃度スライダーの値が変更されたときに、文字色をグレースケールで更新します。
        濃度100%で黒、0%で白になります。

        Args:
            value_str (str): スライダーから渡される現在の値 (文字列型、0-100)。
        """
        density = int(value_str)
        gray_value = int(255 * (100 - density) / 100) # 0(黒) から 255(白) の範囲に変換
        hex_color = f'#{gray_value:02x}{gray_value:02x}{gray_value:02x}' # HEXカラーコードに変換
        self.text_color_var.set(hex_color)

    def _choose_text_color(self): 
        """
        「文字色選択」ボタンが押されたときに呼び出されます。
        カラーピッカーダイアログを表示し、選択された色を文字色として設定します。
        色選択後は、文字濃度スライダーを100% (つまり選択した色がそのまま表示される状態) にリセットします。
        """
        color_code = askcolor(title="文字色を選択", initialcolor=self.text_color_var.get())
        if color_code[1]:
            self.text_color_var.set(color_code[1])
            self.text_density_scale.set(100) # カラーピッカーで色を選んだら濃度は100%とする

    def _get_font(self, font_size, font_family="gothic", is_bold=False):
        """
        指定されたサイズ、ファミリー、太字設定のフォントオブジェクトを取得します。
        フォントはキャッシュされ、再利用されます。プラットフォームごとに適切なフォントパスを探索します。

        Args:
            font_size (int): フォントサイズ (ポイント)。
            font_family (str, optional): フォントファミリーの内部名 (例: "msgothic", "meiryo_ui")。デフォルトは "gothic"。
            is_bold (bool, optional): 太字にするかどうか。デフォルトは False。

        Returns:
            ImageFont.FreeTypeFont: Pillowのフォントオブジェクト。
        """
        font_key = (font_size, font_family, platform.system(), is_bold) # キャッシュキーに太字情報も追加
        if font_key in self.font_cache:
            return self.font_cache[font_key]
        
        font_path = None
        # プラットフォームとフォントファミリー、太字指定に応じたフォントパス候補
        # 各フォントファミリーに対して、[通常フォントパス候補, 太字フォントパス候補] の形式で定義
        font_paths_config = {
            "Windows": {
                "msgothic": (["C:/Windows/Fonts/msgothic.ttc", "arial.ttf"], ["C:/Windows/Fonts/msgothic.ttc", "arialbd.ttf"]), # TTCの場合、太字は同じファイル内の別indexの可能性もあるが、Pillowのtruetypeはindex指定可能
                "msmincho": (["C:/Windows/Fonts/msmincho.ttc", "arial.ttf"], ["C:/Windows/Fonts/msmincho.ttc", "arialbd.ttf"]),
                "meiryo_ui": (["C:/Windows/Fonts/meiryo.ttc", "arial.ttf"], ["C:/Windows/Fonts/meiryob.ttc", "arialbd.ttf"]),
                "yu_gothic_ui": (["C:/Windows/Fonts/YuGothR.ttc", "C:/Windows/Fonts/YuGothic-Regular.ttf", "arial.ttf"], ["C:/Windows/Fonts/YuGothB.ttc", "C:/Windows/Fonts/YuGothic-Bold.ttf", "arialbd.ttf"]),
                "gothic": (["C:/Windows/Fonts/meiryo.ttc", "arial.ttf"], ["C:/Windows/Fonts/meiryob.ttc", "arialbd.ttf"]), # デフォルトゴシック
                "mincho": (["C:/Windows/Fonts/YuMincho.ttc", "arial.ttf"], ["C:/Windows/Fonts/YuMinb.ttc", "arialbd.ttf"])  # デフォルト明朝
            },
            "Darwin": { # macOS
                "gothic": (["/System/Library/Fonts/ヒラギノ角ゴシック W4.ttc", "Arial Unicode.ttf"], ["/System/Library/Fonts/ヒラギノ角ゴシック W7.ttc", "Arial Bold.ttf"]), # ヒラギノはウェイトで太さを表現
                "mincho": (["/System/Library/Fonts/ヒラギノ明朝 ProN W3.ttc", "Arial Unicode.ttf"], ["/System/Library/Fonts/ヒラギノ明朝 ProN W6.ttc", "Arial Bold.ttf"]),
                "msgothic": (["Arial Unicode.ttf"], ["Arial Bold.ttf"]), # macOSにMSフォントは標準搭載なし、Arialで代替
                "msmincho": (["Arial Unicode.ttf"], ["Arial Bold.ttf"]),
                "meiryo_ui": (["Arial Unicode.ttf"], ["Arial Bold.ttf"]), # Meiryoも標準搭載なし
                "yu_gothic_ui": (["/System/Library/Fonts/YuGothic-Regular.otf", "Arial Unicode.ttf"], ["/System/Library/Fonts/YuGothic-Bold.otf", "Arial Bold.ttf"]) # macOSにも游ゴシックは含まれる
            },
            "Linux": { # Linux (フォントは環境依存性が高い)
                "gothic": (["NotoSansCJK-Regular.ttc", "ipag.ttf", "DejaVuSans.ttf"], ["NotoSansCJK-Bold.ttc", "ipagp.ttf", "DejaVuSans-Bold.ttf"]),
                "mincho": (["NotoSerifCJK-Regular.ttc", "ipam.ttf", "DejaVuSans.ttf"], ["NotoSerifCJK-Bold.ttc", "ipamp.ttf", "DejaVuSans-Bold.ttf"]),
                "msgothic": (["DejaVuSans.ttf"], ["DejaVuSans-Bold.ttf"]), # MSフォントの代替
                "msmincho": (["DejaVuSans.ttf"], ["DejaVuSans-Bold.ttf"]),
                "meiryo_ui": (["DejaVuSans.ttf"], ["DejaVuSans-Bold.ttf"]),
                "yu_gothic_ui": (["DejaVuSans.ttf"], ["DejaVuSans-Bold.ttf"])
            }
        }
        
        font_candidates = []
        if platform.system() in font_paths_config:
            platform_fonts = font_paths_config[platform.system()]
            font_family_paths = platform_fonts.get(font_family, ([], []))
            font_candidates = font_family_paths[1] if is_bold else font_family_paths[0]

        # 候補パスを順にチェックし、存在するフォントパスを見つける
        for path_candidate in font_candidates:
            if os.path.exists(path_candidate):
                font_path = path_candidate
                break
        
        # 太字指定で太字フォントが見つからなかった場合、通常フォントで代替しようと試みる
        if is_bold and not font_path and font_family_paths[0]:
            for path_candidate in font_family_paths[0]:
                if os.path.exists(path_candidate):
                    font_path = path_candidate # 通常フォントで代替
                    # print(f"Warning: Bold font for '{font_family}' not found. Using regular weight.")
                    break
        
        try:
            if font_path:
                # PillowのImageFont.truetypeでフォントをロード
                # TTCファイルの場合、太字は別のインデックスにある可能性もあるが、
                # Pillowはフォント名やファイルパスで適切なウェイトを推測しようと試みる
                font = ImageFont.truetype(font_path, font_size)
            else:
                # フォントが見つからない場合はPillowのデフォルトフォントを使用
                # print(f"Warning: Font '{font_family}' (bold: {is_bold}) not found. Using default font.")
                font = ImageFont.load_default() 
        except Exception as e:
            # フォントロード中にエラーが発生した場合もデフォルトフォントを使用
            print(f"Font loading error for '{font_family}' (bold: {is_bold}) at '{font_path}': {e}. Using default.")
            font = ImageFont.load_default()
        
        self.font_cache[font_key] = font
        return font

    def _get_fitted_font_size(self, text_content, rect_width, rect_height, max_font_size=100, font_family="gothic", is_bold=False):
        """
        指定されたテキストが与えられた矩形内に収まる最大のフォントサイズを計算します。
        効率的な探索のために二分探索アルゴリズムを使用します。

        Args:
            text_content (str): 表示するテキスト。
            rect_width (float): テキストを表示する矩形の幅 (ピクセル)。
            rect_height (float): テキストを表示する矩形の高さ (ピクセル)。
            max_font_size (int, optional): 探索するフォントサイズの最大値。デフォルトは100。
            font_family (str, optional): フォントファミリーの内部名。デフォルトは "gothic"。
            is_bold (bool, optional): 太字にするかどうか。デフォルトは False。

        Returns:
            int: 矩形内に収まる最大のフォントサイズ。収まらない場合は0に近い値を返す可能性あり。
        """
        if not text_content or rect_width <= 0 or rect_height <= 0:
            return 0 
        
        min_f_size, low, high, best_f_size = 1, 1, max_font_size, 1 # 最小フォントサイズ、探索範囲の下限・上限、最適なフォントサイズ
        
        # 二分探索で最適なフォントサイズを見つける
        while low <= high:
            mid = (low + high) // 2
            if mid == 0: # フォントサイズ0は無効なのでスキップ
                low = 1
                continue
            
            font = self._get_font(mid, font_family, is_bold) # 現在の試行サイズでフォントを取得
            
            # Pillow 9.0.0 以降では getbbox, 9.2.0 以降では getlength が推奨される場合がある
            # getbbox は (left, top, right, bottom) のタプルを返す
            try:
                bbox = font.getbbox(text_content) # テキストのバウンディングボックスを取得
                text_render_width = bbox[2] - bbox[0]
                text_render_height = bbox[3] - bbox[1]
            except AttributeError: # 古いPillowバージョンなどへのフォールバック
                 text_render_width, text_render_height = font.getsize(text_content)


            if text_render_width <= rect_width and text_render_height <= rect_height:
                best_f_size = mid # 現在のサイズで収まるなら、これが新しい最適候補
                low = mid + 1     # より大きなサイズを試す
            else:
                high = mid - 1    # サイズが大きすぎるので、より小さなサイズを試す
        return best_f_size

    def _save_state(self): 
        """
        アプリケーションの現在の状態（アノテーションリスト、現在のページ、選択情報など）を
        undoスタックにディープコピーして保存します。
        これにより、「元に戻す」機能が実現されます。
        新しい操作が行われると、redoスタックはクリアされます。
        """
        # 保存する状態を定義
        state = {
            'annotations': copy.deepcopy(self.annotations), # アノテーションリスト (重要なのでディープコピー)
            'current_page_index': self.current_page_index,
            # 選択中のアノテーションの座標のみを保存 (オブジェクト自体はannotationsから復元するため)
            'selected_ann_coords': self.selected_ann['coords'] if self.selected_ann else None, 
            # 各ページの回転情報も保存
            'page_rotations': {i: self.doc[i].rotation for i in range(len(self.doc))} if self.doc else {}
        }
        self.undo_stack.append(state)
        if len(self.undo_stack) > self.max_undo_depth: # スタックが最大深度を超えた場合
            self.undo_stack.pop(0) # 最も古い状態を削除 (FIFO)
        
        self.redo_stack.clear() # 新しい操作が加わったので、やり直し履歴はクリア
        self._update_undo_redo_buttons() # undo/redoボタンの有効/無効状態を更新

    def _update_undo_redo_buttons(self): 
        """
        「元に戻す」ボタンの有効/無効状態を、undoスタックの状態に基づいて更新します。
        undoスタックに複数の状態（初期状態＋1つ以上の操作後状態）がある場合に有効になります。
        (redoボタンは現バージョンではUIにないため、undoのみ更新)
        """
        if hasattr(self, 'undo_button') and self.undo_button.winfo_exists(): # undo_buttonが生成済みか確認
            # undoスタックに初期状態以外にも履歴があれば有効 (初期状態は常にスタックの底にある想定)
            can_undo = len(self.undo_stack) > 1 
            self.undo_button.config(state=tk.NORMAL if can_undo else tk.DISABLED)

    def undo_action(self): 
        """
        「元に戻す」操作を実行します。
        undoスタックから直前の状態を復元し、UIを更新します。
        """
        if len(self.undo_stack) > 1: # 初期状態以外に復元可能な状態がある場合
            self._dirty_pages.add(self.current_page_index) # 現在表示中のページは再描画が必要になる可能性
            
            self.undo_stack.pop() # 現在の状態をスタックから取り除く (これにより1つ前の状態がトップになる)
            restored_state = copy.deepcopy(self.undo_stack[-1]) # 復元する状態 (スタックの新しいトップ) を取得
            
            # アプリケーションの状態変数を復元
            self.annotations = restored_state['annotations']
            new_page_index = restored_state['current_page_index']
            
            # ページ回転状態を復元
            if self.doc:
                for idx, rotation in restored_state.get('page_rotations', {}).items():
                    if 0 <= idx < len(self.doc): # ページの存在を確認
                        self.doc[idx].set_rotation(rotation)

            self.selected_ann = None # 選択状態を一旦リセット
            # 復元されたアノテーション座標に基づいて、選択されていたアノテーションを再特定
            if restored_state['selected_ann_coords']:
                for ann in self.annotations: 
                    # ページインデックスと座標が一致するものを探す
                    if ann['coords'] == restored_state['selected_ann_coords'] and \
                       ann['page_idx'] == new_page_index: # 復元後のページインデックスで比較
                        self.selected_ann = ann
                        break
            
            # UIを復元後の状態に更新
            self.page_entry.delete(0, tk.END)
            self.page_entry.insert(0, str(new_page_index))
            
            # ページインデックスが変更された場合は、ダーティページセットにも追加
            if self.current_page_index != new_page_index:
                 self._dirty_pages.add(new_page_index)
            self.current_page_index = new_page_index # ページインデックスを更新

            self.show_page() # ページを再表示 (アノテーションなども再描画される)
            self._update_undo_redo_buttons() # ボタン状態を更新
            if self.selected_ann: # もしアノテーションが再選択されたら、左パネルも更新
                self._update_left_panel_for_selected_ann(self.selected_ann)
        else:
            messagebox.showinfo("情報", "これ以上元に戻せる操作はありません。")

    def select_pdf(self): 
        """
        「PDFを選択」コマンド。
        ファイルダイアログを表示し、ユーザーが選択したPDFファイルを開きます。
        """
        path = filedialog.askopenfilename(filetypes=[("PDFファイル", "*.pdf")])
        if not path: # ファイルが選択されなかった場合 (キャンセルなど)
            return
        self.select_pdf_path(path) # 選択されたパスでPDFを開く処理を呼び出す

    def select_pdf_path(self, path): 
        """
        指定されたパスのPDFファイルを開き、アプリケーションの状態を初期化します。
        既存のドキュメントは閉じられます。

        Args:
            path (str): 開くPDFファイルのフルパス。
        """
        try:
            if self.doc: # 既に別のPDFが開いていれば閉じる
                self.doc.close()
            
            self.doc = fitz.open(path) # PyMuPDFでPDFを開く
            self.pdf_path = path
            self.current_page_index = 0 # 最初のページを表示
            
            # UI要素の更新
            self.filename_label.config(text=os.path.basename(path)) # ファイル名ラベル更新
            self.page_entry.delete(0, tk.END)
            self.page_entry.insert(0, "0")
            
            # アプリケーション状態のリセット
            self.annotations.clear()
            self.canvas_item_to_ann.clear()
            self.selected_ann = None
            self.zoom_scale.set(int(self.zoom_factor * 100)) # ズームをデフォルトに戻す
            self.deselect_all_annotations() # 念のため選択解除処理
            
            # キャッシュクリア
            self._rendered_page_cache.clear()
            self._page_cache_lru.clear()
            self._dirty_pages.clear()
            
            self.show_page() # 最初のページを表示
            self._update_text_preview("") # 新しいPDFを開いた直後はテキストプレビューをクリア
            self._save_state() # 新しいPDFを開いた状態をundoスタックの初期状態として保存
        except Exception as e:
            messagebox.showerror("エラー", f"PDF読み込み失敗: {e}")
            if self.doc: self.doc.close() # エラー時もドキュメントが開いていれば閉じる
            self.doc = None
            self.pdf_path = None
            self.filename_label.config(text="(未選択)")
            self.clear_canvas_and_reset_scroll() # Canvasをクリア

    def set_zoom_factor_from_scale(self, value): 
        """
        ズームスライダーの値が変更されたときに呼び出されます。
        ズーム倍率を更新し、ページを再表示します。

        Args:
            value (str): スライダーから渡される現在の値 (文字列型、パーセント表示)。
        """
        new_zoom = float(value) / 100.0 # パーセントから倍率 (0.0-1.0) に変換
        if self.zoom_factor != new_zoom: # 実際にズーム倍率が変わった場合のみ処理
            self.zoom_factor = new_zoom
            # ズーム変更時は全ページのレンダリングキャッシュが無効になるためクリア
            self._rendered_page_cache.clear()
            self._page_cache_lru.clear()
            self._dirty_pages.clear() # ダーティフラグも一旦クリア (全ページ再描画のため)
            self.show_page()

    def show_page(self): 
        """
        現在のページ (`self.current_page_index`) をCanvasに表示します。
        ページのレンダリングはキャッシュを利用し、必要な場合のみ行います。
        アノテーションの描画、ページ情報ラベルの更新もここで行います。
        """
        if not self.doc: # PDFドキュメントが開かれていない場合は何もしない
            self.clear_canvas_and_reset_scroll()
            self._update_text_preview("")
            return
        
        page_idx = self.current_page_index
        actual_zoom = max(0.01, self.zoom_factor) # ズーム倍率が0以下にならないように保護
        
        # 現在のページの回転角度を取得
        current_rotation = self.doc[page_idx].rotation
        cache_key = (page_idx, actual_zoom, current_rotation) # キャッシュキー (回転情報も含む)
        
        # ページの再レンダリングが必要かどうかの判断:
        # 1. キャッシュに存在しない
        # 2. または、ページがダーティ (アノテーション変更など) である
        needs_rerender = cache_key not in self._rendered_page_cache or page_idx in self._dirty_pages

        if needs_rerender:
            # --- ページのレンダリング処理 ---
            page = self.doc[page_idx]
            # PyMuPDFでページを指定されたズーム倍率でピクセルマップにレンダリング
            # fitz.Matrix(zoom_x, zoom_y) でズームを指定
            pix = page.get_pixmap(matrix=fitz.Matrix(actual_zoom, actual_zoom))
            mode = "RGB" if pix.alpha == 0 else "RGBA" # アルファチャンネルの有無でモード決定
            # ピクセルマップからPillow Imageオブジェクトを生成
            current_pil_image = Image.frombytes(mode, [pix.width, pix.height], pix.samples)
            
            # このPIL画像上に、このページのアノテーションを描画
            self._render_annotations_on_pil(current_pil_image, page_idx, actual_zoom)
            
            # レンダリング結果をキャッシュに保存
            self._rendered_page_cache[cache_key] = current_pil_image
            if page_idx in self._dirty_pages:
                self._dirty_pages.remove(page_idx) # ダーティフラグを解除
            
            # LRUキャッシュの更新
            if cache_key in self._page_cache_lru:
                self._page_cache_lru.remove(cache_key)
            self._page_cache_lru.append(cache_key)
            
            # キャッシュサイズが上限を超えた場合、最も古く使われていないエントリを削除
            if len(self._page_cache_lru) > self.MAX_PAGE_CACHE_SIZE:
                oldest_key = self._page_cache_lru.pop(0)
                if oldest_key in self._rendered_page_cache:
                    del self._rendered_page_cache[oldest_key]
            
            self.page_image_pil = current_pil_image # 表示用のPillow Imageを更新
        else:
            # キャッシュから画像を再利用
            self.page_image_pil = self._rendered_page_cache[cache_key]
            # LRUリスト内でアクセスされたキーを末尾に移動
            if cache_key in self._page_cache_lru:
                self._page_cache_lru.remove(cache_key)
            self._page_cache_lru.append(cache_key)

        # --- Canvasへの表示処理 ---
        # Pillow ImageをTkinter PhotoImageに変換
        self.page_image_tk = ImageTk.PhotoImage(self.page_image_pil)
        self.canvas.delete("page_image") # 既存のページ画像を削除 (タグで管理)
        # Canvasの(0,0)に新しいページ画像を表示 (アンカーは北西)
        self.canvas.create_image(0, 0, anchor="nw", image=self.page_image_tk, tags="page_image")
        # Canvasのスクロール領域を画像のサイズに合わせる
        self.canvas.config(scrollregion=(0, 0, self.page_image_pil.width, self.page_image_pil.height))
        
        # --- Canvas上のアノテーション枠の再描画 ---
        # (アノテーション自体はPIL画像に焼きこまれているが、選択用の枠はCanvas上に別途描画)
        self.canvas.delete("annotation_group") # 既存のアノテーション枠を全て削除
        self.canvas_item_to_ann.clear() # マッピングもクリア
        # 現在のページのアノテーションのみを取得して描画
        page_anns = [ann for ann in self.annotations if ann['page_idx'] == page_idx]
        for ann in page_anns:
            self._draw_annotation_bounding_box_on_canvas(ann, self.canvas_item_to_ann)
        
        self.update_page_info_label() # ページ情報ラベルを更新
        self.highlight_selected_annotation() # 選択中のアノテーションがあればハイライト

        # テキストプレビューの自動更新は行わない (「文字出力」ボタンで明示的に行う)

    def _render_annotations_on_pil(self, pil_image, page_idx, zoom): 
        """
        指定されたPillow Imageオブジェクト (ページのレンダリング結果) に、
        該当ページのアノテーションを描画（焼きこみ）します。
        描画順序 (Zオーダー) も考慮されます。

        Args:
            pil_image (PIL.Image.Image): アノテーションを描画する対象のPillow Imageオブジェクト。
            page_idx (int): アノテーションを描画するページのインデックス。
            zoom (float): 現在の表示ズーム倍率。
        """
        draw = ImageDraw.Draw(pil_image) # Pillowの描画コンテキストを取得
        page_annotations = [ann for ann in self.annotations if ann['page_idx'] == page_idx]

        # アノテーションの描画順序を定義 (値が小さいものが先に描画される = 奥になる)
        def get_render_order(ann): 
            type_order = {
                'redaction': 0,    # リダクション (最奥)
                'mask': 1,         # 黒マスク
                'white_mask': 1,   # 白マスク
                'image_object': 1.5,# 挿入画像
                'graphic_object':2,# 図形 (矩形、楕円など)
                'text_image': 3    # テキスト画像 (最前面)
            }
            return type_order.get(ann.get('type'), 4) # 未定義タイプはさらに前面
        
        sorted_annotations = sorted(page_annotations, key=get_render_order) # 描画順でソート

        for ann in sorted_annotations:
            coords_pdf = ann['coords'] # PDF座標系でのアノテーション座標 (x0, y0, x1, y1)
            # Pillow Image上の描画座標に変換 (ズーム適用)
            x0_pil, y0_pil, x1_pil, y1_pil = [c * zoom for c in coords_pdf]
            pil_bbox_w, pil_bbox_h = x1_pil - x0_pil, y1_pil - y0_pil # 描画領域の幅と高さ

            ann_type = ann.get('type')

            if ann_type == 'redaction':
                # リダクション領域を灰色で塗りつぶし
                draw.rectangle((x0_pil, y0_pil, x1_pil, y1_pil), fill=self.redaction_color)
            elif ann_type == 'mask':
                # マスキング領域を黒色で塗りつぶし
                draw.rectangle((x0_pil, y0_pil, x1_pil, y1_pil), fill=self.mask_color)
            elif ann_type == 'white_mask':
                # 白色マスキング領域を白色で塗りつぶし
                draw.rectangle((x0_pil, y0_pil, x1_pil, y1_pil), fill=self.white_mask_color)
            elif ann_type == 'text_image' and ann.get('text_content', ''):
                # テキスト画像をレンダリング
                text_content = ann.get('text_content', '')
                original_font_size = ann.get('font_size', 100) # アノテーションに保存されたフォントサイズ
                font_family = ann.get('font_family', 'gothic')
                text_color = ann.get('text_color', '#000000')
                is_bold = ann.get('font_bold', False) # 太字情報を取得

                # 描画領域に収まるようにフォントサイズを調整 (ズーム後のピクセルサイズで計算)
                fitted_font_size = self._get_fitted_font_size(text_content, pil_bbox_w, pil_bbox_h, 
                                                              int(original_font_size * zoom), font_family, is_bold)
                if fitted_font_size > 0:
                    font = self._get_font(fitted_font_size, font_family, is_bold)
                    
                    # テキストを矩形の中央（垂直方向）に配置するためのオフセット計算
                    try:
                        text_bbox = font.getbbox(text_content) # (left, top, right, bottom)
                        text_draw_y = y0_pil + (pil_bbox_h - (text_bbox[3] - text_bbox[1])) / 2 - text_bbox[1]
                        text_draw_x = x0_pil - text_bbox[0]
                    except AttributeError: # 古いPillowバージョンへのフォールバック
                        text_width, text_height = font.getsize(text_content)
                        ascent, descent = font.getmetrics() # フォントのベースライン情報
                        text_draw_y = y0_pil + (pil_bbox_h - (ascent + descent)) / 2
                        text_draw_x = x0_pil

                    draw.text((text_draw_x, text_draw_y), text_content, font=font, fill=text_color)

            elif ann_type == 'graphic_object' or (ann_type == 'text_box' and ann.get('shape_kind') == 'rectangle'):
                # 図形描画 (矩形、楕円、直線、フリーハンド)
                # 透明背景の一時的なPillow画像を作成し、そこに図形を描画後、メイン画像に合成
                temp_graphic_pil = Image.new('RGBA', (max(1, int(math.ceil(pil_bbox_w))), max(1, int(math.ceil(pil_bbox_h)))), (0,0,0,0)) # 完全透明
                temp_draw = ImageDraw.Draw(temp_graphic_pil)
                
                shape_kind = ann.get('shape_kind')
                line_color = ann.get('line_color', '#000000')
                line_thickness = max(1, int(ann.get('line_thickness', 1) * zoom)) # ズームに応じた線の太さ (最低1px)
                
                # 各図形タイプに応じた描画 (一時画像内の相対座標で描画)
                if shape_kind == 'rectangle' or ann_type == 'text_box': # text_boxも矩形として描画
                    temp_draw.rectangle([(0,0), (pil_bbox_w-1, pil_bbox_h-1)], outline=line_color, width=line_thickness)
                elif shape_kind == 'oval':
                    temp_draw.ellipse([(0,0), (pil_bbox_w-1, pil_bbox_h-1)], outline=line_color, width=line_thickness)
                elif shape_kind == 'line':
                    spec_data = ann.get('shape_specific_data', {})
                    s_pdf, e_pdf = spec_data.get('start'), spec_data.get('end') # PDF座標での始点・終点
                    if s_pdf and e_pdf:
                        # 一時画像内の相対座標に変換し、線を描画
                        s_rel = ((s_pdf[0]*zoom)-x0_pil, (s_pdf[1]*zoom)-y0_pil)
                        e_rel = ((e_pdf[0]*zoom)-x0_pil, (e_pdf[1]*zoom)-y0_pil)
                        temp_draw.line([s_rel, e_rel], fill=line_color, width=line_thickness)
                elif shape_kind == 'freehand':
                    points_pdf = ann.get('shape_specific_data', {}).get('points', []) # PDF座標での点群
                    if len(points_pdf) > 1:
                        # 一時画像内の相対座標に変換し、フリーハンド線を描画
                        points_rel_pil = [((p[0]*zoom)-x0_pil, (p[1]*zoom)-y0_pil) for p in points_pdf]
                        temp_draw.line(points_rel_pil, fill=line_color, width=line_thickness, joint="curve") # joint="curve"で滑らかに
                
                # 描画した一時画像をメインのPIL画像にアルファ合成で貼り付け
                pil_image.paste(temp_graphic_pil, (int(x0_pil), int(y0_pil)), temp_graphic_pil)
            
            elif ann_type == 'image_object' and pil_bbox_w > 0 and pil_bbox_h > 0:
                # 挿入画像の描画
                image_data_bytes = ann.get('image_data')
                if image_data_bytes:
                    try:
                        img_to_paste_orig = Image.open(io.BytesIO(image_data_bytes))
                        # 描画領域に合わせてリサイズ (アスペクト比維持、高品質フィルタ)
                        img_to_paste_resized = img_to_paste_orig.copy() # コピーしてからリサイズ
                        img_to_paste_resized.thumbnail((int(pil_bbox_w), int(pil_bbox_h)), Image.LANCZOS)
                        
                        paste_x, paste_y = int(x0_pil), int(y0_pil)
                        if img_to_paste_resized.mode != 'RGBA': # アルファチャンネルがない場合は変換
                            img_to_paste_resized = img_to_paste_resized.convert('RGBA')
                        # メインのPIL画像にアルファ合成で貼り付け
                        pil_image.paste(img_to_paste_resized, (paste_x, paste_y), img_to_paste_resized)
                    except Exception as e:
                        print(f"Error rendering pasted image on PIL: {e}") # 画像レンダリングエラーを出力

    def _on_mouse_wheel(self, event): 
        """
        メインCanvas (PDFプレビュー) 上でのマウスホイールイベントを処理し、Canvasを垂直スクロールします。
        プラットフォーム間の差異を吸収します。

        Args:
            event: マウスホイールイベントオブジェクト。
        """
        delta = 0
        if platform.system() == "Windows": delta = int(-1*(event.delta/120))
        elif platform.system() == "Darwin": delta = int(-1*event.delta)
        else: delta = -1 if event.num == 4 else 1 if event.num == 5 else 0
        
        self.canvas.yview_scroll(delta, "units")

    def _draw_annotation_bounding_box_on_canvas(self, ann, item_map): 
        """
        指定されたアノテーションのバウンディングボックス（選択・操作用の枠線）をCanvas上に描画します。
        アノテーションのタイプに応じて枠線の色、太さ、スタイル（破線など）を変更します。
        描画されたCanvasアイテムIDはアノテーション辞書と `item_map` に保存されます。

        Args:
            ann (dict): 描画対象のアノテーションオブジェクト。
            item_map (dict): CanvasアイテムIDとアノテーションオブジェクトをマッピングする辞書 (更新される)。
        """
        coords_pdf = ann['coords']
        coords_canvas = [c * self.zoom_factor for c in coords_pdf] # PDF座標をCanvas座標に変換
        
        # デフォルトの枠線スタイル
        outline_color, width, dash_style = self.default_text_box_outline_color, 1, ()
        ann_type = ann.get('type')

        # アノテーションタイプに応じた枠線スタイル設定
        if ann_type == 'text_box':
            outline_color, width, dash_style = "blue", ann.get('line_thickness', 2), ()
        elif ann_type == 'text_image':
            outline_color, width = "green", 2
        elif ann_type == 'graphic_object':
            outline_color, width = ann.get('line_color', '#000000'), ann.get('line_thickness', 2) # 図形の色を反映
        elif ann_type == 'image_object':
            outline_color, width = "cyan", ann.get('line_thickness', 2) 
        elif ann_type in ['mask', 'white_mask', 'redaction']:
            outline_color, dash_style = "orange", (2,2) # 破線 (点線2px, 空白2px)

        # 既存のCanvasアイテムがあれば更新、なければ新規作成
        existing_item_id = ann.get('canvas_items', {}).get('rect')
        if existing_item_id and self.canvas.winfo_exists() and self.canvas.type(existing_item_id): # アイテムが存在するか確認
             self.canvas.coords(existing_item_id, *coords_canvas)
             self.canvas.itemconfig(existing_item_id, outline=outline_color, width=width, dash=dash_style)
        else:
            rect_id = self.canvas.create_rectangle(*coords_canvas, outline=outline_color, width=width, 
                                                 tags="annotation_group", dash=dash_style) # "annotation_group" タグでグループ化
            if 'canvas_items' not in ann: ann['canvas_items'] = {}
            ann['canvas_items']['rect'] = rect_id # アノテーション辞書にCanvasアイテムIDを保存
            item_map[rect_id] = ann # IDとアノテーションのマップに追加

    def go_to_page_from_entry(self): 
        """
        ページ番号入力欄の値に基づいて、指定されたページに移動します。
        入力値のバリデーションも行います。
        """
        if not self.doc:
            return messagebox.showerror("エラー", "PDFファイルが開かれていません。")
        try:
            idx = int(self.page_entry.get()) # 入力値を取得し整数に変換
            if not (0 <= idx < len(self.doc)): # ページ番号が有効範囲内かチェック
                raise ValueError("ページ番号が範囲外です。")
            if self.current_page_index != idx: # 現在表示中のページと異なる場合のみ移動
                self.current_page_index = idx
                self.show_page()
        except ValueError as e:
            messagebox.showerror("エラー", f"正しいページ番号を入力してください (0〜{len(self.doc)-1})。\n詳細: {e}")

    def prev_page(self): 
        """
        前のページに移動します。現在のページが最初のページでなければ実行されます。
        """
        if self.doc and self.current_page_index > 0:
            self.current_page_index -= 1
            self.page_entry.delete(0, tk.END)
            self.page_entry.insert(0, str(self.current_page_index))
            self.show_page()

    def next_page(self): 
        """
        次のページに移動します。現在のページが最後のページでなければ実行されます。
        """
        if self.doc and self.current_page_index < len(self.doc) - 1:
            self.current_page_index += 1
            self.page_entry.delete(0, tk.END)
            self.page_entry.insert(0, str(self.current_page_index))
            self.show_page()

    def update_page_info_label(self): 
        """
        ページ情報ラベル (例: "1 / 10") を現在のページ番号と総ページ数で更新します。
        """
        if self.doc:
            self.page_info_label.config(text=f"{self.current_page_index + 1} / {len(self.doc)}")
        else:
            self.page_info_label.config(text="- / -") # PDFが開かれていない場合

    def on_canvas_button_press(self, event): 
        """
        メインCanvas上でのマウスボタン押下イベントのハンドラ。
        左クリック:
            - 既存アノテーションのリサイズハンドル上ならリサイズモード開始。
            - 描画モードなら新しい図形の描画開始。
            - それ以外（選択モードでアノテーション外など）なら選択解除。
        右クリックは `on_right_click_select` で処理。

        Args:
            event: マウスボタン押下イベントオブジェクト。
        """
        if not self.page_image_tk: return # ページ未表示なら何もしない
        
        canvas_x, canvas_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y) # Canvas内の座標に変換
        self.drag_start_x, self.drag_start_y = canvas_x, canvas_y # ドラッグ開始点を記録
        self.drag_mode = 'none' # ドラッグモードを初期化

        # --- クリックされた位置のアノテーションを特定 ---
        # find_overlapping でクリック地点に重なるCanvasアイテムIDのリストを取得
        overlapping_items = self.canvas.find_overlapping(canvas_x-1, canvas_y-1, canvas_x+1, canvas_y+1)
        # 重なっているアイテムの中から、現在ページのアノテーションを最前面から順に探す
        # (reversedでリストを逆順にし、Canvasの描画順で手前にあるものを優先)
        clicked_ann = next(
            (self.canvas_item_to_ann[item_id] for item_id in reversed(overlapping_items) 
             if item_id in self.canvas_item_to_ann and self.canvas_item_to_ann[item_id]['page_idx'] == self.current_page_index), 
            None # 見つからなければNone
        )

        if clicked_ann: # アノテーションがクリックされた場合
            self.selected_ann = clicked_ann
            self.highlight_selected_annotation() # 選択ハイライト表示
            self._update_left_panel_for_selected_ann(clicked_ann) # 左パネルのUIを更新

            # --- リサイズハンドルのチェック (左クリック時のみ) ---
            if event.num == 1: # event.num == 1 は左クリック
                ann_coords_canvas = self.canvas.coords(self.selected_ann['canvas_items']['rect'])
                resize_handle_type = self._get_resize_handle(canvas_x, canvas_y, ann_coords_canvas)

                if resize_handle_type != 'none': # リサイズハンドルがクリックされた場合
                    self.drag_mode = 'resize_' + resize_handle_type # 例: 'resize_nw'
                    self.original_ann_coords_canvas = ann_coords_canvas # リサイズ前のCanvas座標を保存
                    self.original_pdf_coords_for_resize = copy.deepcopy(self.selected_ann['coords']) # PDF座標も保存
                    # グラフィックオブジェクトの場合、元の図形固有データも保存 (線の始点終点など)
                    if self.selected_ann.get('type') in ['graphic_object', 'image_object']: # 画像もリサイズ対象
                        self.original_shape_specific_data_for_resize = copy.deepcopy(self.selected_ann.get('shape_specific_data'))
                    return # リサイズモード開始なので、以降の処理は不要

        # --- モードに応じた新規描画/挿入処理 (リサイズモードでない場合) ---
        current_mode = self.draw_mode_var.get()

        if current_mode == "insert_image": # 画像挿入モード
            if event.num == 1: # 左クリックで挿入位置決定
                self._insert_image_at_click(canvas_x, canvas_y)
            return

        if event.num == 1 and (current_mode.startswith("draw_") or current_mode == "textbox"):
            # 描画モード (draw_rectangle, draw_oval, etc.) またはテキストボックスモードで左クリック
            self.drag_mode = 'draw_shape' # 図形描画モードに設定
            self.current_drawing_points_canvas = [(canvas_x, canvas_y)] # 描画開始点を記録
            
            # 描画中のフィードバック用の一時的なCanvasアイテムを作成
            shape_to_draw = "draw_rectangle" if current_mode == "textbox" else current_mode
            line_thick = self.line_thickness_scale.get()
            line_col = self.line_color_var.get()
            
            if shape_to_draw == "draw_rectangle": 
                self.temp_canvas_item_id = self.canvas.create_rectangle(canvas_x, canvas_y, canvas_x, canvas_y,
                                                                      outline=line_col, width=line_thick, dash=()) # 線の色を反映
            elif shape_to_draw == "draw_oval": 
                self.temp_canvas_item_id = self.canvas.create_oval(canvas_x, canvas_y, canvas_x, canvas_y,
                                                                 outline=line_col, width=line_thick, dash=())
            elif shape_to_draw == "draw_line": 
                self.temp_canvas_item_id = self.canvas.create_line(canvas_x, canvas_y, canvas_x, canvas_y,
                                                                 fill=line_col, width=line_thick, dash=())
            # フリーハンドの場合は on_canvas_move_press で線が描画される
            return

        # 上記のどの条件にも当てはまらない左クリック (例: 選択モードで何もない場所をクリック)
        if event.num == 1 and not clicked_ann: # アノテーション外をクリックした場合
            self.deselect_all_annotations() # 全ての選択を解除

    def on_right_click_select(self, event):
        """
        メインCanvas上でのマウス右ボタン押下イベントのハンドラ。
        主に既存アノテーションの選択と移動モード開始のために使用します。

        Args:
            event: マウスボタン押下イベントオブジェクト。
        """
        if not self.page_image_tk: return
        
        canvas_x, canvas_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        self.drag_start_x, self.drag_start_y = canvas_x, canvas_y
        self.drag_mode = 'none'

        overlapping_items = self.canvas.find_overlapping(canvas_x-1, canvas_y-1, canvas_x+1, canvas_y+1)
        clicked_ann = next(
            (self.canvas_item_to_ann[item_id] for item_id in reversed(overlapping_items) 
             if item_id in self.canvas_item_to_ann and self.canvas_item_to_ann[item_id]['page_idx'] == self.current_page_index), 
            None
        )

        if clicked_ann: # アノテーション上で右クリックされた場合
            self.selected_ann = clicked_ann
            self.highlight_selected_annotation()
            self._update_left_panel_for_selected_ann(clicked_ann)

            # 右クリック時は常に移動モードを開始
            self.drag_mode = 'move'
            self.original_ann_coords_canvas = self.canvas.coords(self.selected_ann['canvas_items']['rect'])
            self.initial_pdf_coords_for_move = copy.deepcopy(self.selected_ann['coords']) # 移動前のPDF座標を保存
            return
        else: # アノテーション外で右クリックされた場合
            self.deselect_all_annotations() # 選択を解除

    def _get_resize_handle(self, mouse_x, mouse_y, ann_coords_canvas): 
        """
        マウス座標が、指定されたアノテーションのバウンディングボックスのリサイズハンドル上にあるかを判定します。
        どのハンドル上にあるか (例: 'nw', 'se', 'n', 'e' など) を文字列で返します。

        Args:
            mouse_x (float): マウスのCanvas X座標。
            mouse_y (float): マウスのCanvas Y座標。
            ann_coords_canvas (list): アノテーションのCanvas座標 [x0, y0, x1, y1]。
        Returns:
            str: ハンドルの種類 ('nw', 'ne', 'sw', 'se', 'n', 's', 'w', 'e')。ハンドル上でなければ 'none'。
        """
        x0,y0,x1,y1 = ann_coords_canvas
        handle_area = self.RESIZE_HANDLE_SIZE / 2 # ハンドルの判定領域の半径的なもの

        # 各コーナーハンドル (判定優先度高)
        if (x0 - handle_area <= mouse_x <= x0 + handle_area) and \
           (y0 - handle_area <= mouse_y <= y0 + handle_area): return 'nw' # 左上
        if (x1 - handle_area <= mouse_x <= x1 + handle_area) and \
           (y0 - handle_area <= mouse_y <= y0 + handle_area): return 'ne' # 右上
        if (x0 - handle_area <= mouse_x <= x0 + handle_area) and \
           (y1 - handle_area <= mouse_y <= y1 + handle_area): return 'sw' # 左下
        if (x1 - handle_area <= mouse_x <= x1 + handle_area) and \
           (y1 - handle_area <= mouse_y <= y1 + handle_area): return 'se' # 右下
        
        # 各辺ハンドル
        if (x0 - handle_area <= mouse_x <= x0 + handle_area) and \
           (y0 + handle_area < mouse_y < y1 - handle_area): return 'w'  # 左辺
        if (x1 - handle_area <= mouse_x <= x1 + handle_area) and \
           (y0 + handle_area < mouse_y < y1 - handle_area): return 'e'  # 右辺
        if (y0 - handle_area <= mouse_y <= y0 + handle_area) and \
           (x0 + handle_area < mouse_x < x1 - handle_area): return 'n'  # 上辺
        if (y1 - handle_area <= mouse_y <= y1 + handle_area) and \
           (x0 + handle_area < mouse_x < x1 - handle_area): return 's'  # 下辺
           
        return 'none' # どのハンドル上でもない

    def on_canvas_move_press(self, event): 
        """
        メインCanvas上でマウスボタンが押されたまま移動した (ドラッグ) ときのイベントハンドラ。
        現在の `self.drag_mode` に応じて、図形の描画プレビュー更新、アノテーションの移動、
        またはアノテーションのリサイズプレビュー更新を行います。

        Args:
            event: マウス移動イベントオブジェクト。
        """
        if self.drag_mode == 'none': return # ドラッグモードでなければ何もしない
        
        cur_x, cur_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

        if self.drag_mode == 'draw_shape':
            # --- 図形描画中のプレビュー更新 ---
            shape_being_drawn = "draw_rectangle" if self.draw_mode_var.get() == "textbox" else self.draw_mode_var.get()
            
            if shape_being_drawn == "draw_freehand":
                # フリーハンド描画: 現在の点をリストに追加し、直前の点との間に線を描画
                self.current_drawing_points_canvas.append((cur_x,cur_y))
                if len(self.current_drawing_points_canvas) > 1:
                    p1, p2 = self.current_drawing_points_canvas[-2], self.current_drawing_points_canvas[-1]
                    self.canvas.create_line(p1[0], p1[1], p2[0], p2[1], 
                                           fill=self.line_color_var.get(), 
                                           width=self.line_thickness_scale.get(), 
                                           tags="temp_drawing_feedback") # 一時的な描画用タグ
            elif self.temp_canvas_item_id: # 矩形、楕円、直線の場合
                # 一時的なCanvasアイテムの座標を更新してプレビュー
                self.canvas.coords(self.temp_canvas_item_id, self.drag_start_x, self.drag_start_y, cur_x, cur_y)
        
        elif self.drag_mode == 'move' and self.selected_ann and self.original_ann_coords_canvas:
            # --- アノテーション移動中のプレビュー更新 ---
            dx = cur_x - self.drag_start_x # X方向の移動量
            dy = cur_y - self.drag_start_y # Y方向の移動量
            x0,y0,x1,y1 = self.original_ann_coords_canvas # 移動開始時の元のCanvas座標
            # Canvasアイテムの座標を更新
            self.canvas.coords(self.selected_ann['canvas_items']['rect'], x0+dx, y0+dy, x1+dx, y1+dy)
        
        elif self.drag_mode.startswith('resize_') and self.selected_ann and self.original_ann_coords_canvas:
            # --- アノテーションリサイズ中のプレビュー更新 ---
            orig_x0, orig_y0, orig_x1, orig_y1 = self.original_ann_coords_canvas # リサイズ開始時の元のCanvas座標
            new_x0, new_y0, new_x1, new_y1 = orig_x0, orig_y0, orig_x1, orig_y1 # 更新後の座標 (初期値は元と同じ)
            
            handle_type = self.drag_mode[7:] # 'resize_' の後部分 (例: 'nw', 'e')
            
            # ハンドルの種類に応じて、更新する座標辺を決定
            if 'w' in handle_type: new_x0 = cur_x
            if 'e' in handle_type: new_x1 = cur_x
            if 'n' in handle_type: new_y0 = cur_y
            if 's' in handle_type: new_y1 = cur_y
            
            # 座標の正規化 (x0 < x1, y0 < y1 を維持) しつつCanvasアイテムの座標を更新
            self.canvas.coords(self.selected_ann['canvas_items']['rect'], 
                               min(new_x0, new_x1), min(new_y0, new_y1), 
                               max(new_x0, new_x1), max(new_y0, new_y1))

    def on_canvas_button_release(self, event): 
        """
        メインCanvas上でのマウスボタン離上イベントのハンドラ。
        ドラッグ操作（図形描画、移動、リサイズ）を完了し、変更をアノテーションデータに反映します。

        Args:
            event: マウスボタン離上イベントオブジェクト。
        """
        if self.drag_mode == 'none': return
        
        end_x, end_y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y) # マウス離上時のCanvas座標
        current_draw_mode_val = self.draw_mode_var.get()

        if self.drag_mode == 'draw_shape':
            # --- 図形描画操作の完了 ---
            if self.temp_canvas_item_id: # 一時的なプレビューアイテムがあれば削除
                self.canvas.delete(self.temp_canvas_item_id)
                self.temp_canvas_item_id = None
            self.canvas.delete("temp_drawing_feedback") # フリーハンドの一時線も削除
            
            ann_type, shape_kind, shape_specific_data, coords_pdf_final = None, None, {}, None
            line_color_final = self.line_color_var.get()
            line_thickness_final = self.line_thickness_scale.get()

            if current_draw_mode_val == "draw_freehand":
                if len(self.current_drawing_points_canvas) < 2: # 点が少なすぎる場合は無効
                    self._reset_drag_state(); return
                # Canvas座標をPDF座標に変換
                points_pdf = [(p[0]/self.zoom_factor, p[1]/self.zoom_factor) for p in self.current_drawing_points_canvas]
                # 全ての点を含む最小の矩形 (バウンディングボックス) を計算
                min_x_pdf = min(p[0] for p in points_pdf)
                min_y_pdf = min(p[1] for p in points_pdf)
                max_x_pdf = max(p[0] for p in points_pdf)
                max_y_pdf = max(p[1] for p in points_pdf)
                # 矩形が点や線にならないように最小サイズを確保
                coords_pdf_final = (min_x_pdf, min_y_pdf, max(min_x_pdf + 1, max_x_pdf), max(min_y_pdf + 1, max_y_pdf))
                ann_type, shape_kind = 'graphic_object', 'freehand'
                shape_specific_data = {'points': points_pdf}
            else: # 矩形、楕円、直線、テキストボックス
                # ドラッグ開始点と終了点から正規化されたCanvas座標 (x0<x1, y0<y1)
                x0_c = min(self.drag_start_x, end_x)
                y0_c = min(self.drag_start_y, end_y)
                x1_c = max(self.drag_start_x, end_x)
                y1_c = max(self.drag_start_y, end_y)
                
                if abs(x1_c-x0_c) < 5 or abs(y1_c-y0_c) < 5: # 描画サイズが小さすぎる場合は無効
                    self._reset_drag_state(); return
                
                coords_pdf_final = tuple(c/self.zoom_factor for c in (x0_c,y0_c,x1_c,y1_c)) # PDF座標に変換
                
                if current_draw_mode_val == "textbox": 
                    ann_type = 'text_box'
                    shape_kind = 'rectangle' # テキストボックスは内部的には矩形として扱う
                else: # "draw_rectangle", "draw_oval", "draw_line"
                    ann_type = 'graphic_object'
                    shape_kind = current_draw_mode_val.split('_')[1] # "draw_rectangle" -> "rectangle"
                    if shape_kind == 'line': # 直線の場合、始点と終点をPDF座標で保存
                        shape_specific_data = {
                            'start': (self.drag_start_x/self.zoom_factor, self.drag_start_y/self.zoom_factor), 
                            'end': (end_x/self.zoom_factor, end_y/self.zoom_factor)
                        }
            
            # 新しいアノテーションオブジェクトを作成
            new_annotation = {
                'page_idx': self.current_page_index, 
                'coords': coords_pdf_final, 
                'type': ann_type, 
                'canvas_items': {}, # CanvasアイテムIDはshow_pageで再描画時に設定
                'shape_kind': shape_kind, # 'rectangle', 'oval', 'line', 'freehand' または text_boxの場合は'rectangle'
                'line_color': line_color_final, 
                'line_thickness': line_thickness_final,
                'shape_specific_data': shape_specific_data # 直線やフリーハンドの点情報など
            }
            self.annotations.append(new_annotation)
            self.selected_ann = new_annotation # 新規作成したものを選択状態にする
            
            self._dirty_pages.add(self.current_page_index) # ページが変更されたのでダーティマーク
            self._save_state() # 操作履歴を保存
            self.show_page()   # UIを更新
            if ann_type == 'text_box': # テキストボックス作成後はテキスト入力欄にフォーカス
                self.text_to_add_as_image_entry.delete(0, tk.END)
                self.text_to_add_as_image_entry.focus_set()

        elif self.drag_mode == 'move' and self.selected_ann and self.initial_pdf_coords_for_move:
            # --- アノテーション移動操作の完了 ---
            current_canvas_coords = self.canvas.coords(self.selected_ann['canvas_items']['rect'])
            new_coords_pdf = tuple(c / self.zoom_factor for c in current_canvas_coords) # 移動後のPDF座標
            
            # グラフィックオブジェクトの場合、図形固有のデータも移動量に応じて更新
            if self.selected_ann.get('type') == 'graphic_object':
                dx_pdf = new_coords_pdf[0] - self.initial_pdf_coords_for_move[0] # PDF座標でのX移動量
                dy_pdf = new_coords_pdf[1] - self.initial_pdf_coords_for_move[1] # PDF座標でのY移動量
                spec_data = self.selected_ann.get('shape_specific_data', {})
                if self.selected_ann['shape_kind'] == 'line' and 'start' in spec_data and 'end' in spec_data:
                    spec_data['start'] = (spec_data['start'][0] + dx_pdf, spec_data['start'][1] + dy_pdf)
                    spec_data['end'] = (spec_data['end'][0] + dx_pdf, spec_data['end'][1] + dy_pdf)
                elif self.selected_ann['shape_kind'] == 'freehand' and 'points' in spec_data:
                    spec_data['points'] = [(p[0]+dx_pdf, p[1]+dy_pdf) for p in spec_data['points']]
            
            self.selected_ann['coords'] = new_coords_pdf # アノテーションの座標を更新
            self._dirty_pages.add(self.current_page_index)
            self._save_state()
            self.show_page()

        elif self.drag_mode.startswith('resize_') and self.selected_ann and self.original_pdf_coords_for_resize:
            # --- アノテーションリサイズ操作の完了 ---
            new_bbox_canvas = self.canvas.coords(self.selected_ann['canvas_items']['rect']) # リサイズ後のCanvas座標
            new_bbox_pdf = tuple(c / self.zoom_factor for c in new_bbox_canvas) # PDF座標に変換
            
            old_bbox_pdf = self.original_pdf_coords_for_resize # リサイズ開始時のPDF座標
            old_w_pdf = old_bbox_pdf[2] - old_bbox_pdf[0]
            old_h_pdf = old_bbox_pdf[3] - old_bbox_pdf[1]
            
            # スケールファクタ (X方向、Y方向)
            scale_x = (new_bbox_pdf[2]-new_bbox_pdf[0]) / old_w_pdf if old_w_pdf != 0 else 1
            scale_y = (new_bbox_pdf[3]-new_bbox_pdf[1]) / old_h_pdf if old_h_pdf != 0 else 1
            
            current_ann = self.selected_ann
            current_ann['coords'] = new_bbox_pdf # アノテーションのバウンディングボックス座標を更新
            
            # グラフィックオブジェクトの場合、図形固有データもスケールと位置に応じて更新
            if current_ann.get('type') == 'graphic_object' and self.original_shape_specific_data_for_resize:
                orig_spec_data = self.original_shape_specific_data_for_resize
                new_spec_data = {}
                if current_ann['shape_kind'] == 'line' and 'start' in orig_spec_data and 'end' in orig_spec_data:
                    s_orig, e_orig = orig_spec_data['start'], orig_spec_data['end']
                    # 元のバウンディングボックスの左上を基準とした相対座標をスケーリングし、新しい左上に加算
                    new_spec_data['start'] = (new_bbox_pdf[0] + (s_orig[0]-old_bbox_pdf[0])*scale_x, 
                                              new_bbox_pdf[1] + (s_orig[1]-old_bbox_pdf[1])*scale_y)
                    new_spec_data['end'] =   (new_bbox_pdf[0] + (e_orig[0]-old_bbox_pdf[0])*scale_x, 
                                              new_bbox_pdf[1] + (e_orig[1]-old_bbox_pdf[1])*scale_y)
                elif current_ann['shape_kind']=='freehand' and 'points' in orig_spec_data:
                    new_spec_data['points'] = [
                        (new_bbox_pdf[0] + (p[0]-old_bbox_pdf[0])*scale_x, 
                         new_bbox_pdf[1] + (p[1]-old_bbox_pdf[1])*scale_y) 
                        for p in orig_spec_data.get('points',[])
                    ]
                current_ann['shape_specific_data'] = new_spec_data
            
            self._dirty_pages.add(self.current_page_index)
            self._save_state()
            self.show_page()
        
        self._reset_drag_state() # ドラッグ関連の状態変数をリセット

    def _reset_drag_state(self):
        """ドラッグ操作に関連する一時的な状態変数をリセットします。"""
        self.drag_mode = 'none'
        self.current_drawing_points_canvas = []
        self.original_ann_coords_canvas = None
        self.initial_pdf_coords_for_move = None
        self.original_pdf_coords_for_resize = None
        self.original_shape_specific_data_for_resize = None
        if self.temp_canvas_item_id: # 一時的な描画アイテムが残っていれば削除
            self.canvas.delete(self.temp_canvas_item_id)
            self.temp_canvas_item_id = None
        self.canvas.delete("temp_drawing_feedback")


    def _update_left_panel_for_selected_ann(self, ann):
        """
        選択されたアノテーションのプロパティに基づいて、左パネルのUI要素
        （テキスト入力欄、フォント設定、描画設定など）の内容を更新します。

        Args:
            ann (dict): 選択されたアノテーションオブジェクト。
        """
        ann_type = ann.get('type')

        # --- まず、テキスト関連UIをデフォルトまたはアノテーションの値で更新 ---
        self.text_to_add_as_image_entry.delete(0, tk.END) # いったんクリア
        self.font_size_scale.set(ann.get('font_size', 100)) # テキスト画像ならそのサイズ、なければデフォルト
        self.update_font_size_label(str(self.font_size_scale.get())) # ラベルも更新

        font_family_val = ann.get('font_family', self.font_options_map["ゴシック体 (MS Gothic)"])
        display_font_name = next((d_name for d_name, val in self.font_options_map.items() if val == font_family_val), "ゴシック体 (MS Gothic)")
        self.font_dropdown_tk_var.set(display_font_name)
        self.font_family_var.set(font_family_val)
        
        self.font_bold_var.set(ann.get('font_bold', False)) # 太字状態を反映

        self.text_color_var.set(ann.get('text_color', '#000000'))
        # 文字濃度は色から直接は判断できないため、色選択時は100%にする想定。ここではリセットしない。
        
        if ann_type == 'text_image':
            self.text_to_add_as_image_entry.insert(0, ann.get('text_content', ''))
            self.text_to_add_as_image_entry.focus_set() # テキスト入力欄にフォーカス
        elif ann_type == 'text_box': # テキストボックス選択時もテキスト入力欄にフォーカス
             self.text_to_add_as_image_entry.focus_set()


        # --- 次に、描画設定UI (線の色、太さ) を更新 ---
        # (テキストボックスや図形オブジェクトの場合)
        if ann_type in ['graphic_object', 'text_box', 'image_object']: # 画像も枠線太さを持つ
            self.line_color_var.set(ann.get('line_color', '#000000')) 
            self.line_thickness_scale.set(ann.get('line_thickness', 7 if ann_type != 'image_object' else 2)) # 画像以外はデフォルト7、画像は2
        else: # テキスト画像やマスクなどは、左パネルの描画設定は直接反映しない
            self.line_color_var.set('#000000') # デフォルトに戻す
            self.line_thickness_scale.set(7)   # デフォルトに戻す

    def highlight_selected_annotation(self): 
        """
        現在選択されているアノテーション (`self.selected_ann`) のCanvas上の枠線を
        ハイライト表示 (太い赤線) し、以前ハイライトされていたアノテーションがあれば
        その表示を通常の状態に戻します。
        """
        # --- 前回ハイライトされていたアイテムがあれば、通常表示に戻す ---
        if self.last_highlighted_item_id and self.last_highlighted_item_id in self.canvas_item_to_ann:
            prev_ann = self.canvas_item_to_ann.get(self.last_highlighted_item_id) # 安全に取得
            if prev_ann: # アノテーションがまだ存在する場合
                # 通常時の枠線スタイルを再適用
                outline, width, dash = self.default_text_box_outline_color, 1, ()
                prev_ann_type = prev_ann.get('type')
                if prev_ann_type == 'text_box': 
                    outline, width = "blue", prev_ann.get('line_thickness', 2)
                elif prev_ann_type == 'text_image': 
                    outline, width = "green", 2
                elif prev_ann_type == 'graphic_object': 
                    outline, width = prev_ann.get('line_color', '#000000'), prev_ann.get('line_thickness', 2) # 図形の色を反映
                elif prev_ann_type == 'image_object': 
                    outline, width = "cyan", prev_ann.get('line_thickness', 2)
                elif prev_ann_type in ['mask','white_mask','redaction']: 
                    outline, dash = "orange", (2,2)
                
                # Canvasアイテムが存在するか最終確認してから設定
                if self.canvas.winfo_exists() and self.canvas.type(self.last_highlighted_item_id) == 'rectangle':
                    try:
                        self.canvas.itemconfig(self.last_highlighted_item_id, outline=outline, width=width, dash=dash)
                    except tk.TclError: # アイテムが既に削除されている場合など
                        pass
        self.last_highlighted_item_id = None # リセット

        # --- 現在選択されているアイテムがあればハイライト表示 ---
        if self.selected_ann and self.selected_ann.get('canvas_items', {}).get('rect'):
            item_id = self.selected_ann['canvas_items']['rect']
            # Canvasアイテムが存在するか最終確認してから設定
            if self.canvas.winfo_exists() and self.canvas.type(item_id) == 'rectangle':
                try:
                    self.canvas.itemconfig(item_id, outline=self.selected_rect_color, width=3, dash=()) # ハイライト色と太さ
                    self.last_highlighted_item_id = item_id # 新しいハイライトIDを記録
                except tk.TclError:
                     pass

    def copy_selected_annotation(self):
        """
        現在選択されているアノテーションを内部バッファ (`self.copied_ann`) にディープコピーします。
        """
        if self.selected_ann:
            self.copied_ann = copy.deepcopy(self.selected_ann)
            # messagebox.showinfo("情報", "選択したオブジェクトをコピーしました。") # 必要なら通知
        else:
            messagebox.showinfo("情報", "コピーするオブジェクトが選択されていません。")

    def paste_annotation(self):
        """
        内部バッファにコピーされているアノテーションを現在のページにペースト（複製）します。
        ペーストされたアノテーションは、元の位置からわずかにオフセットされます。
        """
        if not self.copied_ann:
            messagebox.showinfo("情報", "ペーストするオブジェクトがコピーされていません。")
            return
        if not self.doc:
            messagebox.showerror("エラー", "PDFが開かれていません。ペーストできません。")
            return

        self._save_state() # ペースト操作前の状態を保存

        new_ann = copy.deepcopy(self.copied_ann) # コピー元から新しいアノテーションを作成

        # ペースト時に元の位置から少しずらす (PDF座標系でオフセット)
        offset_x_pdf = 10 / self.zoom_factor 
        offset_y_pdf = 10 / self.zoom_factor

        # 新しいアノテーションの座標を更新
        new_coords_list = list(new_ann['coords'])
        new_coords_list[0] += offset_x_pdf
        new_coords_list[1] += offset_y_pdf
        new_coords_list[2] += offset_x_pdf
        new_coords_list[3] += offset_y_pdf
        new_ann['coords'] = tuple(new_coords_list)

        # グラフィックオブジェクトの固有データ (点群など) もオフセット
        if new_ann.get('type') == 'graphic_object' and 'shape_specific_data' in new_ann:
            spec_data = new_ann['shape_specific_data']
            if new_ann.get('shape_kind') == 'line' and 'start' in spec_data and 'end' in spec_data:
                spec_data['start'] = (spec_data['start'][0] + offset_x_pdf, spec_data['start'][1] + offset_y_pdf)
                spec_data['end'] = (spec_data['end'][0] + offset_x_pdf, spec_data['end'][1] + offset_y_pdf)
            elif new_ann.get('shape_kind') == 'freehand' and 'points' in spec_data:
                spec_data['points'] = [(p[0] + offset_x_pdf, p[1] + offset_y_pdf) for p in spec_data['points']]

        new_ann['page_idx'] = self.current_page_index # ペースト先は現在のページ
        new_ann['canvas_items'] = {} # CanvasアイテムIDは再描画時に新たに割り当てられる

        self.annotations.append(new_ann)
        self.selected_ann = new_ann # ペーストしたものを選択状態にする
        
        self._dirty_pages.add(self.current_page_index)
        self.show_page() # UI更新
        self._save_state() # ペースト後の状態を保存

    def delete_selected_annotation(self): 
        """
        現在選択されているアノテーションを削除します。
        削除前に確認ダイアログを表示します。
        """
        if self.selected_ann:
            if messagebox.askyesno("確認", "選択されたオブジェクトを削除しますか？この操作は元に戻せます。"):
                self._save_state() # 削除前の状態を保存
                self._dirty_pages.add(self.selected_ann['page_idx'])
                
                # Canvas上のアイテムを削除
                rect_id_to_delete = self.selected_ann.get('canvas_items', {}).get('rect')
                if rect_id_to_delete and self.canvas.winfo_exists() and self.canvas.type(rect_id_to_delete):
                    self.canvas.delete(rect_id_to_delete)
                
                # アノテーションリストから削除
                self.annotations.remove(self.selected_ann)
                # マッピングからも削除 (念のため)
                if rect_id_to_delete in self.canvas_item_to_ann:
                    del self.canvas_item_to_ann[rect_id_to_delete]
                
                self.selected_ann = None # 選択解除
                self.show_page() # UI更新
                self.deselect_all_annotations() # 左パネルのUIリセットのため
        else:
            messagebox.showinfo("情報", "削除するオブジェクトが選択されていません。")

    def delete_image_in_selected_rect(self): 
        """
        選択されたアノテーションのタイプを「リダクション」(灰色塗り) に変更します。
        実質的に、その領域の内容を隠蔽する操作です。
        """
        if self.selected_ann:
            if messagebox.askyesno("確認", "選択範囲をリダクション（内容を隠蔽）しますか？"):
                self._save_state()
                self.selected_ann['type'] = 'redaction' # タイプをリダクションに変更
                # リダクションに伴い、不要になる可能性のあるキーを削除 (あれば)
                for key_to_remove in ['text_content', 'font_size', 'font_family', 'text_color', 'font_bold', 
                                      'shape_kind', 'shape_specific_data', 'image_data']:
                    if key_to_remove in self.selected_ann:
                        del self.selected_ann[key_to_remove]
                self._dirty_pages.add(self.selected_ann['page_idx'])
                self.show_page()
                self.highlight_selected_annotation() # ハイライト更新 (枠色が変わるため)
        else:
            messagebox.showinfo("情報", "リダクションする範囲が選択されていません。")

    def mask_selected_area_black(self): 
        """選択されたアノテーションのタイプを「マスク」(黒塗り) に変更します。"""
        if self.selected_ann:
            self._save_state()
            self.selected_ann['type'] = 'mask'
            for key_to_remove in ['text_content', 'font_size', 'font_family', 'text_color', 'font_bold', 
                                  'shape_kind', 'shape_specific_data', 'image_data']:
                if key_to_remove in self.selected_ann:
                    del self.selected_ann[key_to_remove]
            self._dirty_pages.add(self.selected_ann['page_idx'])
            self.show_page()
            self.highlight_selected_annotation()

    def mask_selected_area_white(self): 
        """選択されたアノテーションのタイプを「白色マスク」(白塗り) に変更します。"""
        if self.selected_ann:
            self._save_state()
            self.selected_ann['type'] = 'white_mask'
            for key_to_remove in ['text_content', 'font_size', 'font_family', 'text_color', 'font_bold', 
                                  'shape_kind', 'shape_specific_data', 'image_data']:
                if key_to_remove in self.selected_ann:
                    del self.selected_ann[key_to_remove]
            self._dirty_pages.add(self.selected_ann['page_idx'])
            self.show_page()
            self.highlight_selected_annotation()

    def deselect_all_annotations(self, keep_selection_state=False): 
        """
        全てのアノテーションの選択を解除し、関連するUI（左パネルの入力欄など）をデフォルト状態にリセットします。
        ハイライト表示も解除されます。

        Args:
            keep_selection_state (bool, optional): 
                Trueの場合、`self.selected_ann` は変更せず、UIのリセットのみ行います。
                主にモード変更時に内部的に使用されます。デフォルトは False。
        """
        if not keep_selection_state:
            self.selected_ann = None
        
        self.highlight_selected_annotation() # ハイライト表示を更新 (選択がなければ解除される)
        
        # 左パネルのテキスト編集関連UIをデフォルトにリセット
        self.text_to_add_as_image_entry.delete(0,tk.END)
        self.font_size_scale.set(100)
        self.update_font_size_label("100")
        self.font_dropdown_tk_var.set("ゴシック体 (MS Gothic)")
        self.font_family_var.set(self.font_options_map["ゴシック体 (MS Gothic)"])
        self.font_bold_var.set(False) # 太字チェックボックスもリセット
        self.text_color_var.set("#000000")
        self.text_density_scale.set(100)
        
        # 左パネルの描画設定UIは、直前の設定を維持するため、ここではリセットしない
        # self.line_color_var.set("#000000")
        # self.line_thickness_scale.set(7)

    def add_text_as_image_to_selection(self): 
        """
        「選択範囲に追加/更新」ボタンのコマンド。
        現在選択されているアノテーション (枠/図形) に、左パネルで設定されたテキスト、
        フォントサイズ、フォントファミリー、太字、色を適用し、タイプを 'text_image' に変更します。
        """
        if not self.selected_ann:
            return messagebox.showinfo("情報", "テキストを追加/更新する枠または図形を選択してください。")
        
        self._save_state() # 操作前の状態を保存
        
        # 選択中のアノテーションのプロパティを更新
        self.selected_ann.update({
            'type': 'text_image', # タイプをテキスト画像に変更
            'text_content': self.text_to_add_as_image_entry.get(),
            'font_size': self.font_size_scale.get(),
            'font_family': self.font_family_var.get(),
            'font_bold': self.font_bold_var.get(), # 太字の状態を追加
            'text_color': self.text_color_var.get()
        })
        
        # text_imageタイプに不要な可能性のあるキーを削除 (元が図形だった場合など)
        for key_to_remove in ['shape_kind', 'shape_specific_data', 'image_data', 'line_color', 'line_thickness']:
            if key_to_remove in self.selected_ann:
                del self.selected_ann[key_to_remove]
        
        self._dirty_pages.add(self.selected_ann['page_idx'])
        self.show_page() # UI更新
        self.highlight_selected_annotation() # ハイライト更新 (枠色が変わる可能性)

    def clear_pdf_selection(self): 
        """
        「PDFをクリア」コマンド。
        現在開いているPDFの選択を解除し、アプリケーションの状態を初期化（未選択状態に）します。
        未保存の変更は失われるため、確認ダイアログを表示します。
        """
        if self.doc:
            if messagebox.askyesno("確認", "PDFの選択をクリアしますか？\n未保存の変更は失われます。"):
                self.doc.close()
                self.doc = None
                self.pdf_path = None
                self.filename_label.config(text="(PDFファイル:未選択)")
                self.current_page_index = 0
                self.annotations.clear()
                self.canvas_item_to_ann.clear()
                self.selected_ann = None
                self.clear_canvas_and_reset_scroll()
                self.update_page_info_label()
                self.undo_stack.clear()
                self._save_state() # クリア後の初期状態を保存
                self._update_undo_redo_buttons()
                self._rendered_page_cache.clear()
                self._page_cache_lru.clear()
                self._dirty_pages.clear()
                self._update_text_preview("") # テキストプレビューもクリア
        else:
            messagebox.showinfo("情報", "クリアするPDFが選択されていません。")

    def reload_pdf(self): 
        """
        「PDFを再読み込み」コマンド。
        現在開いているPDFファイルをディスクから再読み込みします。
        未保存の変更は失われるため、確認ダイアログを表示します。
        """
        if self.pdf_path:
            if messagebox.askyesno("確認", "PDFを再読み込みしますか？\n現在の編集内容は失われます。"):
                current_path = self.pdf_path
                # 一旦クリアしてから再度同じパスで開くことで再読み込みを実現
                # (clear_pdf_selection は内部で undo_stack.clear() も行う)
                if self.doc: self.doc.close() # 先に閉じる
                self.doc=None; self.pdf_path=None; self.filename_label.config(text="(未選択)")
                self.current_page_index=0; self.annotations.clear(); self.canvas_item_to_ann.clear()
                self.selected_ann=None; self.clear_canvas_and_reset_scroll(); self.update_page_info_label()
                self.undo_stack.clear(); self._rendered_page_cache.clear(); self._page_cache_lru.clear(); self._dirty_pages.clear()
                self._update_text_preview("")

                self.select_pdf_path(current_path) # 同じパスで再度開く (内部で _save_state が呼ばれる)
        else:
            messagebox.showinfo("情報", "再読み込みするPDFが選択されていません。")

    def clear_canvas_and_reset_scroll(self): 
        """
        メインCanvasの内容を全てクリアし、スクロール領域をリセットします。
        ページ画像関連のインスタンス変数もリセットします。
        主にPDFが選択されていない状態やクリアされた状態にするために使用します。
        """
        self.canvas.delete("all") # Canvas上の全ての描画アイテムを削除
        self.canvas.config(scrollregion=(0,0,0,0)) # スクロール領域をリセット
        self.page_image_pil = None
        self.page_image_tk = None # Tkinter PhotoImageもNoneに

    def _save_pdf_key_bind(self, event): 
        """Ctrl+S (またはCmd+S) キーバインドでPDF保存関数を呼び出すためのイベントハンドラ。"""
        self.save_pdf()

    def _hex_to_rgb(self, hex_color):
        """
        HEXカラーコード文字列をPyMuPDFが使用するRGBタプル (0.0-1.0) に変換します。
        例: "#FF0000" -> (1.0, 0.0, 0.0)
        """
        hex_color = hex_color.lstrip('#')
        # 16進数文字列を2文字ずつに区切り、整数に変換し、255で割って0.0-1.0の範囲にする
        return tuple(int(hex_color[i:i + 2], 16) / 255.0 for i in (0, 2, 4))

    def _create_preview_pdf_data(self):
        """
        現在のドキュメントとアノテーションに基づいて、プレビュー用のPDFデータをメモリ上に生成します。
        save_pdfメソッドのロジックを流用し、ファイル保存の代わりにバイトデータを返します。

        Returns:
            bytes or None: 生成されたPDFのバイトデータ。エラー時はNone。
        """
        if not self.doc:
            return None

        try:
            preview_doc = fitz.open() # プレビュー用の新しい空のPDFドキュメント
            for page_idx in range(len(self.doc)):
                original_page = self.doc[page_idx]
                # 元のページと同じサイズで新しいページを作成し、元のページの内容をコピー
                new_page = preview_doc.new_page(width=original_page.rect.width,
                                                height=original_page.rect.height)
                new_page.show_pdf_page(new_page.rect, self.doc, page_idx)
                new_page.set_rotation(original_page.rotation) # 元のページの回転を適用

                # 現在のページに適用されているアノテーションのみをフィルタリング
                page_annotations = [ann for ann in self.annotations if ann['page_idx'] == page_idx]
                
                # アノテーションの描画順序を定義 (値が小さいものが先に描画される = 奥になる)
                def get_save_order(ann): 
                    type_order = {'redaction':0, 'mask':1, 'white_mask':1, 'image_object':1.5, 'graphic_object':2, 'text_image':3}
                    return type_order.get(ann.get('type'), 4)
                sorted_annotations = sorted(page_annotations, key=get_save_order)

                # まずリダクションを適用 (PyMuPDFのリダクションは他の描画より先に行う必要がある)
                has_redactions = False
                for ann in sorted_annotations:
                    if ann.get('type') == 'redaction':
                        # リダクションアノテーションを追加し、灰色で塗りつぶす
                        new_page.add_redact_annot(fitz.Rect(ann['coords']), text=" ", fill=(0.75,0.75,0.75))
                        has_redactions = True
                if has_redactions:
                    new_page.apply_redactions(images=fitz.PDF_REDACT_IMAGE_PIXELS) # リダクションを適用して内容を削除

                # その他のアノテーションを描画
                for ann in sorted_annotations:
                    coords_pdf, ann_type = ann['coords'], ann.get('type')
                    rect_fitz = fitz.Rect(coords_pdf) # PyMuPDFのRectオブジェクトに変換
                    
                    if ann_type == 'mask':
                        # 黒色マスキング領域を塗りつぶし
                        new_page.draw_rect(rect_fitz, color=fitz.utils.getColor("black"), fill=fitz.utils.getColor("black"), overlay=True)
                    elif ann_type == 'white_mask':
                        # 白色マスキング領域を塗りつぶし
                        new_page.draw_rect(rect_fitz, color=fitz.utils.getColor("white"), fill=fitz.utils.getColor("white"), overlay=True)
                    elif ann_type == 'text_image' and ann.get('text_content',''):
                        # テキスト画像をPDFに挿入
                        text_content = ann.get('text_content', '')
                        font_size = ann.get('font_size', 100)
                        font_family = ann.get('font_family', 'gothic')
                        text_color = ann.get('text_color', '#000000')
                        is_bold = ann.get('font_bold', False)
                        
                        # テキストが矩形に収まるフォントサイズを計算
                        fitted_font_size = self._get_fitted_font_size(text_content, rect_fitz.width, rect_fitz.height, font_size, font_family, is_bold)
                        if fitted_font_size > 0:
                            font = self._get_font(fitted_font_size, font_family, is_bold)
                            
                            # Pillowでテキストを透明な画像としてレンダリング
                            try:
                                text_bbox_pil = font.getbbox(text_content)
                                img_w_pil, img_h_pil = text_bbox_pil[2]-text_bbox_pil[0], text_bbox_pil[3]-text_bbox_pil[1]
                            except AttributeError: # 古いPillowバージョンへのフォールバック
                                img_w_pil, img_h_pil = font.getsize(text_content)
                                text_bbox_pil = (0,0,img_w_pil, img_h_pil)

                            if img_w_pil > 0 and img_h_pil > 0:
                                text_pil = Image.new('RGBA', (img_w_pil,img_h_pil), (0,0,0,0)) # 透明な背景
                                # テキストを描画 (Pillowのfillは色、PyMuPDFのfillは塗りつぶし)
                                ImageDraw.Draw(text_pil).text((-text_bbox_pil[0],-text_bbox_pil[1]), text_content, font=font, fill=text_color)
                                
                                # 画像をバイトデータに変換し、PDFに挿入
                                img_bytes = io.BytesIO()
                                text_pil.save(img_bytes, format='PNG')
                                new_page.insert_image(rect_fitz, stream=img_bytes.getvalue(), overlay=True)
                    elif ann_type == 'graphic_object' or (ann_type == 'text_box' and ann.get('shape_kind') == 'rectangle'):
                        # 図形（矩形、楕円、直線、フリーハンド）をPDFに描画
                        bbox_pdf = ann['coords']
                        bbox_w, bbox_h = bbox_pdf[2]-bbox_pdf[0], bbox_pdf[3]-bbox_pdf[1]
                        if bbox_w <=0 or bbox_h <=0: continue # 無効なサイズはスキップ
                        
                        shape_kind = ann.get('shape_kind')
                        # アノテーションに保存された線の色をRGBタプルに変換
                        color_rgb = self._hex_to_rgb(ann.get('line_color','#000000')) 
                        thick = ann.get('line_thickness',1)
                        
                        if shape_kind == 'rectangle' or ann_type == 'text_box':
                            # 矩形を描画 (塗りつぶしなし、線のみ)
                            new_page.draw_rect(rect_fitz, color=color_rgb, width=thick, overlay=True)
                        elif shape_kind == 'oval':
                            # 楕円を描画 (塗りつぶしなし、線のみ)
                            new_page.draw_oval(rect_fitz, color=color_rgb, width=thick, overlay=True)
                        elif shape_kind == 'line':
                            # 直線を描画
                            s, e = ann.get('shape_specific_data',{}).get('start'), ann.get('shape_specific_data',{}).get('end')
                            if s and e:
                                new_page.draw_line(fitz.Point(s), fitz.Point(e), color=color_rgb, width=thick, overlay=True)
                        elif shape_kind == 'freehand':
                            # フリーハンド線を描画 (点と点を線で結ぶ)
                            points = ann.get('shape_specific_data',{}).get('points',[])
                            if len(points)>1:
                                for i in range(len(points)-1):
                                    p1 = fitz.Point(points[i])
                                    p2 = fitz.Point(points[i+1])
                                    new_page.draw_line(p1,p2,color=color_rgb,width=thick,overlay=True)
                    elif ann_type == 'image_object':
                        # 挿入画像をPDFに挿入
                        image_data_bytes = ann.get('image_data')
                        if image_data_bytes:
                            try:
                                new_page.insert_image(rect_fitz, stream=image_data_bytes, overlay=True)
                            except Exception as e_img_prev:
                                print(f"Error inserting image to preview PDF page {page_idx}: {e_img_prev}") # 画像挿入エラーを出力
            
            # 生成されたPDFをバイトデータとして取得し、閉じる
            pdf_bytes = preview_doc.tobytes(garbage=4, deflate=True, clean=True)
            preview_doc.close()
            return pdf_bytes
        except Exception as e_prev_create:
            messagebox.showerror("プレビュー生成エラー", f"プレビュー用PDFの生成中にエラーが発生しました: {e_prev_create}")
            if 'preview_doc' in locals() and not preview_doc.is_closed: # エラー時もドキュメントが開いていれば閉じる
                preview_doc.close()
            return None

    def show_processed_preview(self):
        """
        「加工後プレビュー」ボタンのコマンド。
        現在の編集内容を反映したPDFをメモリ上で生成し、新しいウィンドウで表示します。
        """
        if not self.doc:
            messagebox.showinfo("情報", "プレビューするPDFが開かれていません。")
            return

        pdf_bytes = self._create_preview_pdf_data()
        if pdf_bytes:
            # プレビューウィンドウを開く
            PreviewWindow(self.root, pdf_bytes, title=f"加工後プレビュー: {os.path.basename(self.pdf_path or '未保存ドキュメント')}")
        else:
            messagebox.showerror("プレビューエラー", "加工後PDFの生成に失敗したため、プレビューを表示できません。")


    def save_pdf(self): 
        """
        現在のPDFドキュメントに適用された全てのアノテーションを反映させ、
        新しいPDFファイルとして保存します。保存先はファイルダイアログで指定します。
        """
        if not self.doc:
            return messagebox.showerror("エラー", "保存するPDFが開かれていません。")
        
        # 保存ファイル名とパスをユーザーに尋ねる
        default_filename = f"edited_{os.path.basename(self.pdf_path or 'document.pdf')}"
        output_path = filedialog.asksaveasfilename(defaultextension=".pdf", 
                                                 filetypes=[("PDFファイル", "*.pdf")], 
                                                 initialfile=default_filename)
        if not output_path: # キャンセルされた場合
            return
        
        try:
            # 加工済みPDFデータをメモリ上に生成
            processed_pdf_bytes = self._create_preview_pdf_data()
            if not processed_pdf_bytes:
                raise Exception("加工済みPDFデータの生成に失敗しました。")

            # バイトデータをファイルに書き込む
            with open(output_path, "wb") as f:
                f.write(processed_pdf_bytes)
            
            messagebox.showinfo("保存完了", f"編集されたPDFを '{output_path}' に保存しました。")
        except Exception as e_save:
            messagebox.showerror("エラー", f"PDF保存中にエラーが発生しました: {e_save}")


    def split_pdf(self): 
        """
        「PDF分割」コマンド。
        ユーザーが選択したPDFファイルを各ページに分割し、個別のPDFファイルとして保存します。
        """
        # まず、分割したいPDFファイルを選択させる
        input_pdf_path = filedialog.askopenfilename(
            title="分割するPDFファイルを選択",
            filetypes=[("PDFファイル", "*.pdf")]
        )
        if not input_pdf_path: # ファイルが選択されなかった場合
            return

        # 次に、分割したPDFを保存するディレクトリを選択させる
        output_dir = filedialog.askdirectory(
            title="分割されたPDFを保存するフォルダを選択"
        )
        if not output_dir: # フォルダが選択されなかった場合
            return

        try:
            source_doc = fitz.open(input_pdf_path) # 選択されたPDFファイルを開く
            base_filename = os.path.splitext(os.path.basename(input_pdf_path))[0] # 元のファイル名（拡張子なし）
            
            # 各ページを個別のPDFとして保存
            for i in range(len(source_doc)):
                page = source_doc[i]
                new_pdf = fitz.open() # 新しい空のPDFを作成
                new_pdf.insert_pdf(source_doc, from_page=i, to_page=i) # 現在の1ページのみを挿入
                
                output_filepath = os.path.join(output_dir, f"{base_filename}_page_{i+1}.pdf")
                new_pdf.save(output_filepath)
                new_pdf.close() # 作成したPDFを閉じる

            source_doc.close() # 元のPDFを閉じる
            messagebox.showinfo("PDF分割完了", f"PDFファイル '{os.path.basename(input_pdf_path)}' の各ページを\n'{output_dir}' に分割して保存しました。")

        except Exception as e:
            messagebox.showerror("PDF分割エラー", f"PDFの分割中にエラーが発生しました: {e}")


    def merge_pdfs(self): 
        """
        「PDF結合」コマンド。
        複数のPDFファイルを選択し、現在開いているPDFに結合するか、または選択したPDF同士を新しいPDFとして結合します。
        """
        # 現在PDFが開かれていない場合、新規結合するかどうかをユーザーに確認
        if not self.doc and not messagebox.askyesno("確認", "現在PDFが開かれていません。\n選択した複数のPDFを新規ファイルとして結合しますか？\nファイル選択した順番が結合の順番となります。\nctrl+クリックで複数選択可能"):
             messagebox.showinfo("情報", "結合操作を中止しました。")
             return
        elif not self.doc: # PDFが開かれていないが、新規結合を選択した場合
            base_doc_for_merge = fitz.open() # 空のドキュメントをベースにする
            is_merging_to_new = True
            initial_merge_filename = "merged_document.pdf"
        else: # PDFが開かれている場合
            # 現在のPDFに結合するか、新規ファイルとして結合するかをユーザーに確認
            is_merging_to_new = not messagebox.askyesno("結合方法の選択", "現在開いているPDFに他のPDFを結合しますか？\n\n('いいえ' を選択すると、選択した複数のPDFを\n新しいPDFファイルとして結合します。)")
            if is_merging_to_new:
                base_doc_for_merge = fitz.open() # 新規結合用の空ドキュメント
                initial_merge_filename = "merged_document.pdf"
            else:
                base_doc_for_merge = self.doc # 現在のドキュメントに追記
                initial_merge_filename = f"merged_{os.path.basename(self.pdf_path or 'document.pdf')}"


        files_to_merge = filedialog.askopenfilenames(title="結合するPDFファイルを選択 (複数選択可)",
                                                    filetypes=[("PDFファイル","*.pdf")])
        if not files_to_merge: # ファイル選択がキャンセルされた場合
            if is_merging_to_new and base_doc_for_merge and not base_doc_for_merge.is_closed: # 新規結合用に作った空ドキュメントを閉じる
                base_doc_for_merge.close()
            return

        # 新規結合の場合、最初にベースとなるPDF (もしあれば現在のdoc) を追加リストに含めるか選択させる
        # (このロジックは複雑になるため、今回は「現在のPDFに結合」or「選択した複数ファイルを新規結合」の2択に絞る)

        output_merge_path = filedialog.asksaveasfilename(defaultextension=".pdf", initialfile=initial_merge_filename)
        if not output_merge_path:
            if is_merging_to_new and base_doc_for_merge and not base_doc_for_merge.is_closed: # base_doc_for_merge が存在し、閉じられていない場合
                base_doc_for_merge.close()
            return

        try:
            for file_path_to_add in files_to_merge:
                # 自分自身への結合はスキップ
                if not is_merging_to_new and file_path_to_add == self.pdf_path: 
                    messagebox.showinfo("情報",f"'{os.path.basename(file_path_to_add)}' は現在開いているPDFのため、結合対象からスキップします。", parent=self.root)
                    continue
                with fitz.open(file_path_to_add) as temp_add_doc:
                    base_doc_for_merge.insert_pdf(temp_add_doc) # ページを追記
            
            base_doc_for_merge.save(output_merge_path) # 結合結果を保存
            messagebox.showinfo("成功",f"PDFを結合し、'{output_merge_path}' に保存しました。",parent=self.root)
            
            # 結合後のPDFをアプリで開く (新規結合の場合、または現在のドキュメントに追記した場合)
            if is_merging_to_new or base_doc_for_merge == self.doc : 
                self.select_pdf_path(output_merge_path) 
        except Exception as e_merge:
            messagebox.showerror("エラー",f"PDF結合エラー:\n{e_merge}",parent=self.root)
        finally: # base_doc_for_merge が self.doc と異なる (つまり新規作成された) 場合のみ閉じる
            if is_merging_to_new and base_doc_for_merge and not base_doc_for_merge.is_closed:
                base_doc_for_merge.close()


    def rotate_current_page(self):
        """
        「ページ回転」コマンド。
        現在表示されているページを時計回りに90度回転させます。
        回転はPDFドキュメントオブジェクトに直接適用され、表示も更新されます。
        """
        if not self.doc:
            messagebox.showerror("エラー", "PDFファイルが開かれていません。")
            return
        
        self._save_state() # 回転操作前の状態を保存
        
        current_page_obj = self.doc[self.current_page_index]
        current_rotation_angle = current_page_obj.rotation
        new_rotation_angle = (current_rotation_angle + 90) % 360 # 90度加算し、360で剰余を取る
        
        current_page_obj.set_rotation(new_rotation_angle) # ページの回転を設定
        
        # ページが回転したため、関連するキャッシュをクリアし、再描画を強制
        self._dirty_pages.add(self.current_page_index) # 現在のページをダーティとしてマーク
        
        self.show_page() # ページを再表示してUIを更新
        # undoボタンの状態更新は_save_state内で行われる

    def _insert_image_at_click(self, canvas_x, canvas_y):
        """
        画像挿入モードでCanvasがクリックされたときに呼び出されます。
        画像ファイル選択ダイアログを表示し、選択された画像をPDFのクリック位置に追加します。
        画像の初期サイズはCanvas幅の一定割合を上限として調整されます。

        Args:
            canvas_x (float): 画像を挿入する基準となるCanvas X座標。
            canvas_y (float): 画像を挿入する基準となるCanvas Y座標。
        """
        if not self.doc:
            messagebox.showerror("エラー", "まずPDFファイルを開いてください。"); return
        
        image_path_selected = filedialog.askopenfilename(
            title="挿入する画像ファイルを選択", 
            filetypes=[("画像ファイル", "*.png *.jpg *.jpeg *.gif *.bmp *.tiff"), ("すべてのファイル", "*.*")]
        )
        if not image_path_selected: return # キャンセルされた場合
        
        try:
            with open(image_path_selected, "rb") as img_file_handle:
                image_data_bytes_content = img_file_handle.read() # 画像をバイトデータとして読み込み
            
            # Pillowで画像のオリジナルサイズを取得
            pil_temp_img = Image.open(io.BytesIO(image_data_bytes_content))
            img_original_w, img_original_h = pil_temp_img.size
            pil_temp_img.close()
            
            # クリックされたCanvas座標をPDF座標に変換 (画像の左上隅とする)
            x0_pdf_coord, y0_pdf_coord = canvas_x/self.zoom_factor, canvas_y/self.zoom_factor
            
            # 画像の初期表示サイズを計算 (ここではCanvas表示幅の30%を最大幅の目安とする)
            # ただし、PDF座標系でのサイズで計算する
            initial_display_scale = 0.3 
            # Canvasの現在の表示幅をPDF座標系に換算し、その半分を最大幅とする
            max_display_width_pdf = (self.canvas.winfo_width() / self.zoom_factor) * 0.5 
            
            initial_width_pdf = img_original_w * initial_display_scale
            if initial_width_pdf > max_display_width_pdf: # 最大幅を超えないように調整
                initial_width_pdf = max_display_width_pdf
            
            aspect_ratio = img_original_h / img_original_w if img_original_w > 0 else 1
            initial_height_pdf = initial_width_pdf * aspect_ratio
            
            # 画像のPDF座標系でのバウンディングボックスを計算
            x1_pdf_coord = x0_pdf_coord + initial_width_pdf
            y1_pdf_coord = y0_pdf_coord + initial_height_pdf
            final_coords_pdf = (x0_pdf_coord, y0_pdf_coord, x1_pdf_coord, y1_pdf_coord)
            
            # 新しい画像アノテーションを作成
            new_image_ann = {
                'page_idx': self.current_page_index, 
                'coords': final_coords_pdf, 
                'type': 'image_object', 
                'image_data': image_data_bytes_content, 
                'canvas_items': {},
                'line_thickness': self.line_thickness_scale.get() # 枠線の太さも保存
            }
            self.annotations.append(new_image_ann)
            self.selected_ann = new_image_ann # 挿入した画像を選択状態にする
            
            self._dirty_pages.add(self.current_page_index)
            self._save_state()
            self.show_page()
        except Exception as e_insert_img:
            messagebox.showerror("画像挿入エラー", f"画像の読み込みまたは挿入中にエラーが発生しました:\n{e_insert_img}")

    def extract_text_to_preview(self):
        """
        「文字出力」ボタンのコマンド。
        現在のPDFページからテキストを抽出し、右パネルのテキストプレビュー領域に表示します。
        """
        if not self.doc:
            self._update_text_preview("PDFファイルが開かれていません。")
            return
        
        try:
            page_to_extract = self.doc[self.current_page_index]
            self._update_text_preview_from_page(page_to_extract)
        except Exception as e_extract:
            self._update_text_preview(f"テキスト抽出エラー: {e_extract}")

    def _update_text_preview_from_page(self, page_obj):
        """
        指定されたPyMuPDFのPageオブジェクトからテキストを抽出し、テキストプレビューを更新するヘルパー関数。

        Args:
            page_obj (fitz.Page): テキストを抽出するページオブジェクト。
        """
        try:
            extracted_text_content = page_obj.get_text() # PyMuPDFのget_text()でテキスト抽出
            self._update_text_preview(extracted_text_content)
        except Exception as e_update_text:
            self._update_text_preview(f"テキスト抽出中にエラーが発生しました: {e_update_text}")

    def _update_text_preview(self, text_to_display):
        """
        テキストプレビューウィジェットの内容を指定されたテキストで更新するヘルパー関数。

        Args:
            text_to_display (str): 表示するテキスト。
        """
        self.text_output.config(state="normal") # 一時的に編集可能にする
        self.text_output.delete(1.0, tk.END)    # 既存のテキストをクリア
        self.text_output.insert(tk.END, text_to_display) # 新しいテキストを挿入
        self.text_output.config(state="disabled")# 再度読み取り専用に戻す

# === プレビューウィンドウクラス ===
class PreviewWindow(tk.Toplevel):
    """
    加工後のPDFをプレビュー表示するための新しいウィンドウ。
    """
    def __init__(self, master, pdf_bytes, title="加工後PDFプレビュー"):
        """
        PreviewWindowのコンストラクタ。

        Args:
            master: 親ウィンドウ (通常はメインアプリケーションのルートウィンドウ)。
            pdf_bytes (bytes): 表示するPDFのバイトデータ。
            title (str, optional): ウィンドウのタイトル。
        """
        super().__init__(master)
        self.title(title)
        self.geometry("800x600") # プレビューウィンドウの初期サイズ

        self.pdf_doc = None # プレビュー用PDFドキュメント
        self.current_page_num = 0 # プレビューウィンドウで現在表示中のページ番号 (0始まり)
        self.pil_image = None # 表示用Pillowイメージ
        self.tk_image = None  # 表示用Tkinterイメージ
        self.preview_zoom_factor = 1.0 # プレビューウィンドウ専用のズーム倍率

        try:
            self.pdf_doc = fitz.open(stream=pdf_bytes, filetype="pdf")
        except Exception as e:
            messagebox.showerror("プレビューエラー", f"プレビュー用PDFの読み込みに失敗しました:\n{e}", parent=self)
            self.destroy() # エラー時はウィンドウを閉じる
            return

        if len(self.pdf_doc) == 0:
            messagebox.showinfo("情報", "プレビューするページがありません。", parent=self)
            self.destroy()
            return
        
        self._setup_ui()
        self._show_preview_page()

        self.protocol("WM_DELETE_WINDOW", self._on_close) # 閉じるボタンの処理

    def _setup_ui(self):
        """プレビューウィンドウのUI要素をセットアップします。"""
        # --- トップフレーム (コントロール類) ---
        top_frame = tk.Frame(self)
        top_frame.pack(side="top", fill="x", pady=5)

        tk.Button(top_frame, text="<< 前のページ", command=self._prev_page).pack(side="left", padx=5)
        self.page_label = tk.Label(top_frame, text="ページ: -/-")
        self.page_label.pack(side="left", padx=5)
        tk.Button(top_frame, text="次のページ >>", command=self._next_page).pack(side="left", padx=5)

        tk.Label(top_frame, text="倍率(%):").pack(side="left", padx=(10,0))
        self.zoom_scale = Scale(top_frame, from_=20, to=300, resolution=10, orient=HORIZONTAL,
                                command=self._set_zoom_from_scale, length=150)
        self.zoom_scale.set(int(self.preview_zoom_factor * 100))
        self.zoom_scale.pack(side="left", padx=5)

        tk.Button(top_frame, text="閉じる", command=self._on_close).pack(side="right", padx=10)

        # --- メインフレーム (Canvasとスクロールバー) ---
        main_frame = tk.Frame(self, bd=1, relief=tk.SUNKEN)
        main_frame.pack(side="bottom", fill="both", expand=True, padx=5, pady=5)

        self.v_scroll = tk.Scrollbar(main_frame, orient="vertical")
        self.v_scroll.pack(side="right", fill="y")
        self.h_scroll = tk.Scrollbar(main_frame, orient="horizontal")
        self.h_scroll.pack(side="bottom", fill="x")

        self.canvas = tk.Canvas(main_frame, bg="lightgrey",
                                yscrollcommand=self.v_scroll.set,
                                xscrollcommand=self.h_scroll.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.v_scroll.config(command=self.canvas.yview)
        self.h_scroll.config(command=self.canvas.xview)
        
        # マウスホイールでのスクロール
        self.canvas.bind("<MouseWheel>", self._on_preview_mouse_wheel)
        self.canvas.bind("<Button-4>", self._on_preview_mouse_wheel)
        self.canvas.bind("<Button-5>", self._on_preview_mouse_wheel)


    def _show_preview_page(self):
        """現在のページをプレビューCanvasに表示します。"""
        if not self.pdf_doc or self.current_page_num < 0 or self.current_page_num >= len(self.pdf_doc):
            return

        page = self.pdf_doc[self.current_page_num]
        pix = page.get_pixmap(matrix=fitz.Matrix(self.preview_zoom_factor, self.preview_zoom_factor))
        mode = "RGB" if pix.alpha == 0 else "RGBA"
        self.pil_image = Image.frombytes(mode, [pix.width, pix.height], pix.samples)
        self.tk_image = ImageTk.PhotoImage(self.pil_image)

        self.canvas.delete("all") # 既存の描画をクリア
        self.canvas.create_image(0, 0, anchor="nw", image=self.tk_image)
        self.canvas.config(scrollregion=(0, 0, self.pil_image.width, self.pil_image.height))
        
        self.page_label.config(text=f"ページ: {self.current_page_num + 1}/{len(self.pdf_doc)}")

    def _prev_page(self):
        if self.current_page_num > 0:
            self.current_page_num -= 1
            self._show_preview_page()

    def _next_page(self):
        if self.pdf_doc and self.current_page_num < len(self.pdf_doc) - 1:
            self.current_page_num += 1
            self._show_preview_page()
            
    def _set_zoom_from_scale(self, value_str):
        self.preview_zoom_factor = float(value_str) / 100.0
        self._show_preview_page()

    def _on_preview_mouse_wheel(self, event):
        delta = 0
        if platform.system() == "Windows": delta = int(-1*(event.delta/120))
        elif platform.system() == "Darwin": delta = int(-1*event.delta)
        else: delta = -1 if event.num == 4 else 1 if event.num == 5 else 0
        self.canvas.yview_scroll(delta, "units")

    def _on_close(self):
        """プレビューウィンドウを閉じる際の処理。"""
        if self.pdf_doc:
            self.pdf_doc.close()
            self.pdf_doc = None
        self.destroy()


# === アプリケーションのエントリーポイント ===
if __name__ == "__main__":
    root_window = tk.Tk() # Tkinterのルートウィンドウを作成
    app_instance = PDFEditorApp(root_window) # アプリケーションのインスタンスを生成
    
    def on_main_window_closing():
        """ウィンドウが閉じられるときに呼び出される処理。開いているPDFドキュメントを安全に閉じます。"""
        if app_instance.doc and not app_instance.doc.is_closed: # ドキュメントが開いていれば
            app_instance.doc.close() # 閉じる
        root_window.destroy() # ルートウィンドウを破棄してアプリケーションを終了
    
    # ウィンドウの閉じるボタン("X")が押されたときの動作を on_main_window_closing 関数に設定
    root_window.protocol("WM_DELETE_WINDOW", on_main_window_closing) 
    
    root_window.mainloop() # Tkinterのイベントループを開始 (これによりウィンドウが表示され、イベント処理が始まる)
