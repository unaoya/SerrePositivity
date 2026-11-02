# DG-W3：名前解決と universe 順序の静的事前調査（2026-11-02）

**ビルド・Lean 実行なし。重点照合する短名の候補は 1 ファイル 4 箇所。universe 行は 608 元すべてで順序・section 内の配置を保持する。草案・本番 Lean・既存道具は変更していない。**

基点は `infra/dg-w2` の `12b6b5c13`。main の取り込みコミット `3ea13677a` と、全 Lean ソース・W3 草案・merge_modules.py の差は 0。新しい main の merge や W3 の適用はしていない。命名案と private_renames は承認済みのまま。

## 1. 調べた範囲と方法

48 統合先・608 元（5 ディレクトリ）。追跡された本番ソース 31,792 モジュールと Mathlib 8,603 モジュールの import と宣言を読み、統合後の import 和・付け替えをメモリ上で構成した。Archive は除外。前後とも import グラフの循環なし。

統合元内部では「統合先の import 和＋自分より前の元の宣言」だけを可視とした。後続の元の本文を先行する元から使えるとは数えない。外側の利用元は推移閉包で比較した。閉包が増えるのは **10,567 本＝統合元 606＋外側 9,961**。

新たに届く同名宣言を、無修飾 token の現在の名前空間・親名前空間（ルートも含む）と照合した。namespace/section、部分的な `end`、`open … in`、選択的 open を区別する。元から同じ深さ以上の名前空間で見えている候補 38 出現は除外し、局所束縛と構造体のフィールドを別扱いにした。

静的索引は 395,846 名（明示宣言と直接書かれたフィールド・構築子）。既存 W2 after snapshot のうち現在のソース本文と完全一致する 112 モジュールを使い、索引の公開・明示宣言 **5,211 名を照合して欠落 0**。snapshot の再採取はしていない。namespace/section の走査診断も 0。

これは Lean の名前解決器ではない。マクロ・notation・型依存の解決・instance/coercion、間接生成される全宣言までは静的に確定しない。Lean/Std 等の toolchain モジュールは import ノードとして扱い、宣言索引には含めない。従って「候補以外は必ず安全」とはしない。

## 2. 名前解決の重点候補：HomotopyCategory 4 箇所

利用元は `SerrePositivity/InfinityCategories/DGNerve/HomotopyCategory.lean`。20 行の `open CategoryTheory DifferentialGraded` による従来の候補は `SerrePositivity.DifferentialGraded.HomotopyCategory`（元 `Category/Homotopy.lean:61`、W3 後は `Category.Basic` 内）。

| 行 | 宣言（名前空間 HomotopyComparison 内） | 短名 |
| ---: | --- | --- |
| 34 | `toH0` | `HomotopyCategory A D` |
| 98 | `equivalence` | `HomotopyCategory A D` |
| 104 | `fromH0` | `HomotopyCategory A D` |
| 109 | `counitIso` | `HomotopyCategory A D` |

W3 後に **Mathlib のルート名 `HomotopyCategory`**（`Mathlib/Algebra/Homology/HomotopyCategory.lean:45`）が新たに届く。次の import 経路を独立に探索し、before では到達せず after では到達することを確認した。

```text
InfinityCategories.DGNerve.HomotopyCategory
→ InfinityCategories.DGNerve.ClosedComposition
→ InfinityCategories.DGNerve.EdgeHomotopy
→ DifferentialGraded.Category.Basic（統合先）
→ DifferentialGraded.Complexes.Perturbation（統合先）
→ Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
→ Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
→ Mathlib.Algebra.Homology.HomotopyCategory.Shift
→ Mathlib.Algebra.Homology.HomotopyCategory
```

`Complexes.Perturbation` の import 和にこの経路を持ち込む元は **`Complexes.SphereHom`**。単に Category.Homotopy を改名することで生じる差ではなく、別の束の import 和が推移的に届く事例である。

§14 の DGFunctor.op は同じ名前空間への追加だったが、今回はルート祖先への同名追加であり、優先順位や型による候補選択が同じになるとは限らない。**失敗・解決先変更を確定したものではない**。W3 の before/after で上表 4 宣言を重点照合する。もし従来先を明示する修飾が必要なら、候補は `SerrePositivity.DifferentialGraded.HomotopyCategory`。今は変更せず、指示書の保存比較手順に従って確認する。

同じ名前空間・親名前空間（ルートを除く）に新たに届く宣言による、§14 と同型の追加候補は今回の索引では 0。

## 3. 除外した構造体フィールドの 3 出現

`DifferentialGraded/Presentation/Category.lean:52` の `differential` は `DGComplexPresentationCode` のフィールド宣言、54 行の 2 出現はその先行フィールドを参照する。新たに届く大域名 `SerrePositivity.DifferentialGraded.differential`（`Category/Components.lean:19`）との文字列一致として抽出されたが、open 経由の大域名使用ではない。修飾候補から除外した。判定を JSON に残す。

## 4. universe 行の順序と配置

608 本すべてに universe コマンドが 1 本（22 種類の並び）あり、すべて最初の明示宣言より前にある。各元の行を生成した named section の直後と逐語的に照合し、**608/608 一致**。統合先の先頭に universe の和がないことも確認した。

旧方式で先頭に和を置いた場合、順序が変わる元は次の 4 本。現在の修正済み道具では元の順序を保持する。

| 元（DG 接頭辞省略） | 行 | 統合先 | 元の順序＝現在の生成順序 | 旧方式の射影 |
| --- | ---: | --- | --- | --- |
| `Category.IdempotentTelescope` | 17 | `Category.Basic` | `v u` | `u v` |
| `Category.EquivalenceComparison` | 9 | `Category.Basic` | `v u v' u'` | `u v u' v'` |
| `Derived.AssociatorMiddleRestrictionResolved` | 27 | `Derived.Functor` | `u v w z t s` | `u v w t z s` |
| `Derived.AssociatorSecondMiddleRestrictionResolved` | 26 | `Derived.Functor` | `u v w z t s` | `u v w t z s` |

今回確認したのはソース行とスコープの静的な保持。level parameter の実際の順序・型ハッシュは W3 の before/after snapshot で確認する。特に上表は回帰確認の対象とし、宇宙引数の順序差を表示だけの差として処理しない。

## 5. 草案の現時点の check

```sh
python3 -B scripts/refactor/merge_modules.py \
  scripts/refactor/targets/dg-w3-merge-plan.json \
  --area SerrePositivity.DifferentialGraded --check --max-lines 1700 \
  --report /tmp/dg-w3-review-dryrun.md
```

終了 0。48 統合先・608 元、最大 **1,621 行**、1,700 行超過 0、private 衝突 0。警告 601 件は無名 section の閉じ補完だけ。既存の private_renames 3 箇所は維持した。

以前の `dg-w3-merge-dryrun.md` は 611 元・最大 1,601 行の時点の記録である。D3 の 3 元除外と universe 修正後の現在値は本報告を用いる。

全出現の判定・608 元の行順序・閉包の経路・入力 SHA-256 は [機械可読記録](dg-w3-static-review-2026-11-02.json)。再現用の作業スクリプト、生成候補 48 本、check の全文、展開対象一覧は作業木の `.lake/verify/dg-w3-static-review-2026-11-02/` に保存した。生成候補は静的検査用で、本番へ適用していない。
