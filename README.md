# SerreNumberTheory

セール『数論講義』の内容を Lean 4 で形式化するプロジェクトです．

## 形式化の構成
形式化した Lean ファイルは章ごとに配置しています．

```text
SerreNumberTheory/
└── Chapter01/
    ├── S010101FiniteFields.lean
    ├── S010102MultiplicativeGroup.lean
    ├── S010201PowerSums.lean
    └── S010202ChevalleyWarning.lean
```

形式化ファイルは，書籍内での位置がわかるように番号をつけています．
例えば，
```text
S 01 01 01 FiniteFields .lean
  │  │  │
  │  │  └─ 項目番号
  │  └──── 節番号
  └─────── 章番号
```
です．

## Verso ドキュメント (Literate Documentation)

[Verso ドキュメント](https://are4c4.github.io/SerreNumberTheory/) は，Lean 4 の公式ドキュメント生成ツール [Verso](https://github.com/leanprover/verso) を用いてビルドされたインタラクティブな Web ドキュメントです．

- ソースコード内の型ホバー情報・定義参照
- タクティックごとのゴール（証明状態）表示
- 検索機能および KaTeX による数式表示

ローカルでビルドする場合：
```bash
lake build :literateHtml
```
ビルド結果は `.lake/build/literate-html` に生成されます．

## Notion Viewer

[Notion Viewer](https://are4c4.github.io/SerreNumberTheory/notion/) は，Lean の定理や定義を Notion 上で読みやすく表示するために作成した静的 Viewer です．

GitHub Pages 上で公開しています．

Lean のソースコードに加えて，構文ハイライト・証明状態・ goal などを表示でき，形式化した内容を Notion から参照しやすくします．

例えば，「[表示例](https://are4c4.github.io/SerreNumberTheory/notion/?decl=SerreNumberTheory.field_char_is_prime_or_zero)」のように表示できます．

## 関連リンク
- [Verso ドキュメント (Web)](https://are4c4.github.io/SerreNumberTheory/)
- [Notion Viewer](https://are4c4.github.io/SerreNumberTheory/notion/)
- [Viewer URL生成](https://are4c4.github.io/SerreNumberTheory/notion/link/)
- [GitHub Repository](https://github.com/are4c4/SerreNumberTheory)

## 参考文献
- J.-P. セール 著，彌永健一 訳，『数論講義』，岩波書店，オンデマンド版，2017年，ISBN 978-4-00-730592-4．