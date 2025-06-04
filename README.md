PDF編集ツール仕様書

概要

本アプリケーションは、Tkinterを用いて構築されたGUIベースのPDF編集ツールです。PyMuPDF（fitz）によるPDF処理、Pillowによる画像処理、TkinterによるUI構築を統合し、アノテーション追加、ページ操作、画像・文字追加、マスク処理など、多彩なPDF編集機能を提供します。

機能一覧

1. ファイル操作

PDFファイルの選択、クリア、再読み込み

編集済みPDFの保存（Ctrl+S対応）

PDF情報の表示（ファイル名、ページ数など）

2. ページ操作

ページ移動（前へ、次へ、直接指定）

ページの回転（90度単位）

表示倍率（ズーム）の変更（スライダー/Ctrl+ホイール）

テキスト抽出と表示

加工後のプレビュー表示

3. アノテーション

アノテーションの種類：

テキスト枠

矩形、楕円、直線、フリーハンド

画像挿入

マスク（黒、白）

リダクション（灰色塗り）

テキストを画像として追加

アノテーション選択・移動・リサイズ・削除

アノテーションのコピー＆ペースト

アノテーション描画色、線の太さ、文字色、フォント、フォントサイズ、太字設定、濃度調整

4. Undo/Redo

最大20履歴までの操作の取り消し（Ctrl+Z）

状態保存と復元に copy.deepcopy を使用

5. モード選択

UI上のプルダウンメニューで各種描画/操作モードを選択

モードごとのカーソル変更とUI有効/無効切替

6. UI構成

左パネル：ファイル操作・ツール・ページ操作・描画設定・アノテーション操作・文字設定

右パネル：PDFプレビュー、テキスト出力表示

スクロール、ズーム、操作説明を含むインタラクティブなUI

技術構成

GUI：Tkinter

PDF処理：PyMuPDF（fitz）

画像処理：Pillow

カラー選択：tkinter.colorchooser

Undo/Redo：スタック構造による履歴管理

フォント処理：プラットフォーム別フォント対応、キャッシュあり

拡張性

Redo機能の実装余地あり（スタック構造は準備済み）

アノテーションのZオーダー管理可能

複数ページへの一括適用なども今後可能

注意事項

フォントパスはOSに依存するため、対応フォントがない場合はデフォルトフォントを使用

undo履歴が20件を超えると古いものから破棄

ズーム変更時は全ページのキャッシュがクリアされる

バージョン

PDF編集ツール v1.4

ライセンス

PyMuPDF, Pillow, Tkinterに準ずる

PDF Editor Tool

A GUI-based PDF annotation and editing tool built with Tkinter. It integrates PyMuPDF (fitz) for PDF operations and Pillow for image processing, allowing users to draw annotations, insert images and text, redact content, and more.

Features

🗂 File Management

Open, reload, and clear PDF files

Save annotated PDFs (Ctrl+S)

Display file name and page info

📄 Page Control

Navigate pages (previous, next, jump to page)

Rotate pages (90 degrees)

Adjust zoom via slider or Ctrl + Mouse Wheel

Extract and display page text

Preview with annotations applied

✍️ Annotations

Supported annotation types:

Text box

Rectangle, ellipse, line, freehand

Insert image

Mask (black/white)

Redaction (gray fill)

Add text as image

Select, move, resize, delete annotations

Copy & paste annotations

Customize color, thickness, font, size, boldness, and density

↩ Undo/Redo

Undo up to 20 actions (Ctrl+Z)

Uses copy.deepcopy for state preservation

🧭 Mode Selection

Dropdown to switch between draw/edit modes

Cursor and UI state adapt per mode

🖥 UI Layout

Left Panel: File tools, page tools, draw settings, annotation editing, text input

Right Panel: PDF preview (Canvas) and text output

Scroll and zoom supported

Tech Stack

GUI: Tkinter

PDF Engine: PyMuPDF (fitz)

Image Processing: Pillow

Color Picker: tkinter.colorchooser

Font Handling: OS-dependent font resolution with caching

Extensibility

Redo stack prepared for future implementation

Z-order control supported

Potential for batch multi-page annotation

Limitations

Font availability depends on OS; default font used if not found

Only 20 undo states retained

Zooming clears render cache for all pages

Version

PDF Editor Tool v1.4

License

Follows respective licenses for PyMuPDF, Pillow, and Tkinter.

Screenshot

(Insert image of the app UI here)

Getting Started

pip install PyMuPDF Pillow
python pdf_editor.py

Author

Developed with ❤️ for interactive PDF annotation tasks.
