# K-L9（Sp・ホモトピー群）

## 所有するもの・借りるもの

- 所有：Kan 複体の π_n とその群構造・自然性・ホモトピー不変性。
- 所有：Kan fibration の連結射とホモトピー長完全列。
- 所有：γ-B の Ω スペクトル、その単体的圏と coherent nerve。
- 所有：整数次数のスペクトルの π_n。
- 所有：有理化、hG、Tot の Kan 複体による実構成。
- 借用：H_* は K-L2 が所有する。
- 借用：pro 形式は K-L6 が所有する。
- 借用：γ1 は N レーンの局所 Kan coherent nerve 定理。
- 借用：γ3 は N レーンのホモトピー極限と ∞ 極限の比較。
- 借用：Core の pinched 写像空間とその Kan 性。
- 既存 Spectra は比較用に読むだけで編集しない。
- 既存 HomotopicalAlgebra は読むだけで編集しない。
- 既存 InfinityCategories は読むだけで編集しない。

## 1. 正本と目的

作成日：2026-10-18。
状態：L9a 着手。L9c の写像空間の局所 Kan 性に設計確認点がある。
正本：[KST 経路](../k-theory-kst-route.md) §5、§13 決定 3・4。
基盤の正本：[foundations](../foundations.md) §1 の F3・γ。
本文は実装順と検証状態を管理する。
実施の経緯はコミットメッセージに記録する。
証明できた宣言だけを完了表に記載する。
設計案は実装済み宣言と区別する。
全体の到達点は定理 3.1 の全次数 π_* 同型である。
本レーン単独で定理 3.1 全体を証明したとは主張しない。
`theorem_3_1_K0` の置換は合流先の仕事である。
`supportedRankK0_descent` の置換も合流先の仕事である。
本レーンはそのための Sp と π_* を供給する。

## 2. 編集範囲

Lean の作業場所は `SerrePositivity/KST/Spectra/`。
namespace は `SerrePositivity.KST.Spectra`。
集約入口は `SerrePositivity/KST/Spectra.lean`。
ルートへの変更はこの入口の public import 一行のみ。
監査入口は `scripts/audit_kst_spectra.lean`。
この計画以外のレーン計画を編集しない。
共有ファイルの既存の未コミット変更を保存する。
他者の新規ファイルをコミットしない。
他者の作業を修正してビルドを迂回しない。
import 閉包の破損はそのまま報告する。

## 3. 原典の対応

| 対象 | 原典 | 適用の範囲 |
| --- | --- | --- |
| Kan 複体 | Kerodon §3.1 | ホーンの充填 |
| pointed homotopy | Kerodon §3.2.1 | 基点を固定したホモトピー |
| π_n の定義 | Kerodon §3.2.2 | 境界が定数の単体の商 |
| π_n の積 | Kerodon §3.2.3 | 充填で定義する群構造 |
| 可換性 | Kerodon §3.2.3 | n ≥ 2 の二つの積の比較 |
| π_* による検出 | Kerodon Theorem 3.2.7.1 | Kan 複体の同値 |
| coherent nerve | HTT Proposition 1.1.5.10 | 局所 Kan から quasicategory |
| coherent nerve | Kerodon Proposition 2.4.5.1 | γ1 の既存実装 |
| pinched Hom | HTT Proposition 1.2.2.3 | 右写像空間 |
| pinched Hom | Kerodon Proposition 4.6.5.5 | Core の Kan 性 |
| spectra | HA §1.4.2 | spectrum objects |
| spaces の spectra | HA §1.4.3 | 安定ホモトピー群との接続 |
| 比較 | HTT Theorem 4.2.4.1 | γ3 後の ∞ 極限の比較 |
| 単体的 π_* | Goerss–Jardine, I §7 | 古典的ホモトピー群 |
| fiber の連結射 | Kerodon §3.2.5、Goerss–Jardine, I §§7–8 | 相対ホーンと完全性 |
| 長完全列 | Kerodon Theorem 3.2.6.1 | kernel と image の比較 |
| スペクトルの比較 | Bousfield–Friedlander, §2 | 古典的スペクトル |

原典の定理番号が未確認の場合は節番号を使う。
原典の主張を公理として持ち込まない。
原典への参照は証明義務の代わりにしない。
Mathlib の既存証明は依存公理まで監査する。

## 4. 全体の設計決定

γ は γ-B を採用する。
HT-KQ の引用を使わない。
`Inputs/Homotopy/KanQuillen` を import しない。
既存の対称スペクトルを Sp の定義に置き換えない。
Sp の入口は Mathlib の `SimplicialNerve`。
γ1 の既存定理で quasicategory を得る。
その前に豊穣 Hom の Kan 性を証明する。
Kan 性を新しい入力仮定として隠さない。
群の法則を未証明の入力構造にしない。
fiber 長完全列を仮説として構造に入れない。
有理化の π_* 計算を入力として構造に入れない。
π_* 同型が第 1 段の公開界面となる。
Sp の ∞ 極限という主張は γ3 後に分離する。

## 5. 次数と基点

Kan 複体の次数は自然数。
次数ゼロは pointed set で、一般には群でない。
群構造は正の次数だけに付ける。
可換群構造は二以上の次数に付ける。
基点は `X _⦋0⦌` の元。
射の像の基点は自然変換の零成分で与える。
基点を固定する射と、基点を動かす道を区別する。
ホモトピー不変性はまず基点固定で証明する。
非可換な π_1 の積の向きを明記する。
スペクトルの次数は整数。
負次数を自然数への切り捨てで定義しない。
段の選択への独立性を遷移同型で証明する。

## 6. L9a：代表と関係

Mathlib の `SSet.PtSimplex` を使う。
境界定数条件は `RelativeMorphism` の条件に従う。
本レーン固有の名前で商を定義する。
Mathlib の将来の `π_n` と衝突させない。
`RelStruct` のホーンによる関係を使う。
正次数では `MulStruct .const f g i` との比較を使う。
反射性は退化単体から得る。
対称性は `oneMulEqSymm` から得る。
推移性は `oneMulEqTrans` から得る。
各面添字の関係が一致することは別途証明する。
零次数は `PiZero` と照合する。
商の等式から関係の証人へ戻す補題を用意する。
代表の変更が積に影響しないことを先に証明する。

## 7. L9a：群構造

積の候補は `MulStruct.nonempty` から選ぶ。
選択の依存を商で消す。
積の候補の一意性は商でだけ主張する。
代表単体の一意性は主張しない。
単位元は定数単体の類。
左単位は `oneMul` から得る。
右単位は `mulOne` から得る。
結合則は `MulStruct.assoc` と `assoc'` を使う。
左逆元は `exists_left_inverse` から選ぶ。
群構造を商の上に構成する。
逆元の代表選択は群法則による一意性で処理する。
二つの積の interchange を充填で証明する。
Eckmann–Hilton により二以上の次数の可換性を得る。
可換性に π_* の安定化を先取りしない。

## 8. L9a：自然性とホモトピー

単体集合の射による代表単体の後合成を定義する。
境界定数条件の保存を証明する。
`RelStruct` の後合成を定義する。
`MulStruct` の後合成を定義する。
商上の写像を定義する。
恒等射の保存を証明する。
合成の保存を証明する。
積の保存を証明する。
基点付き同型が誘導する群同型を構成する。
相対ホモトピーから代表単体間の関係を得る。
ホモトピーの両端の誘導写像が一致すると示す。
ホモトピー同値から群同型を得る。
ここまでを L9a の完了条件とする。

## 9. L9b：fiber と連結射

対象は Kan fibration。
基点は全空間で選び、底の基点へ送る。
fiber は基点への引き戻し。
fiber の Kan 性を引き戻しから証明する。
底の代表単体をホーンに沿って持ち上げる。
欠けた面が fiber の代表単体となることを示す。
持ち上げの選択が商上で独立であると示す。
連結射の基点保存を示す。
適切な正次数で群準同型性を示す。
fiber → 全空間 → 底の誘導射を定義する。
連続する射の合成が零となると示す。
各箇所で kernel = image を証明する。
π_1 と π_0 の端は pointed set の完全性で述べる。
fibration 間の射に対する自然性を示す。
ここまでを L9b の完了条件とする。

## 10. L9c：ループ空間

基点付き Kan 複体のループ対象を具体的に固定する。
区間の両端の制限の fiber とする候補がある。
Core の pinched Hom を使う候補もある。
二つの具体モデルを無言で同一視しない。
Kan 性は端点制限の fibration 性から得る。
基点は定数ループ。
ループ構成の関手性を証明する。
π_n(ΩX) と π_(n+1)(X) の比較を証明する。
比較は基点と積を保存する。
Ω の enriched functor としての振る舞いも必要となる。

## 11. L9c：スペクトルと写像空間

指定された対象データは X_n と X_n ≅ ΩX_(n+1)。
同型は単体集合の厳密な同型として読むのが現行指定。
HA の spectrum object の構造同値と区別する。
対象の構造同型を保つ射を定義する。
段ごとの pointed Hom は Kan である。
段の整合条件を課した Hom は極限として記述できる。
ただし一般の Kan 複体の極限は Kan とは限らない。
したがって「極限だから Kan」という証明は使えない。
必要なのはこの特定の図式の追加の充填性の証明である。
逆系の遷移射の fibration 性は十分条件の候補。
その fibration 性を仮定として追加することはしない。
厳密 Hom を homotopy coherent Hom に替えるなら設計変更となる。
構造同型を弱同値に替える場合も設計変更となる。
その変更を L9 が独断で採用しない。
局所 Kan 性が得られてから coherent nerve を作る。
γ1 の適用条件を実際に満たすことを監査する。
整数次数 π_* とその自然性を構成する。
fiber 列の定義と長完全列を実装する。
ここまでを L9c の完了条件とする。

## 12. L9d：有理化

自然数による乗法写像の telescope を構成する。
全ての正整数を反転する列を明示する。
通常の余極限と homotopy telescope を区別する。
構成した対象の Kan 性を証明する。
ループ構造との整合を示す。
π_* が必要な telescope と可換すると示す。
アーベル群の有理化との比較を構成する。
比較の対象は π_*(X) ⊗ ℚ。
自然性と加法性を証明する。
有理化写像の π_* を明記する。
ここまでを L9d の完了条件とする。

## 13. L9e：作用と Tot

有限群の作用を実際の作用図式として与える。
homotopy fixed points と通常の fixed points を区別する。
cosimplicial replacement の全ての構造射を構成する。
Tot は段ごとの Kan 複体で構成する。
Tot の Kan 性を Reedy 型の充填で証明する。
極限という語だけから Kan 性を主張しない。
有理係数の有限群コホモロジー消滅を実証する。
平均化に使う群の位数が可逆であることを明示する。
自明作用の有理スペクトル M の比較射を作る。
π_* 上で M → M^{hG} の同型を証明する。
任意の非有理 M に同じ結論を主張しない。
γ3 前は Sp の ∞ 極限の普遍性を主張しない。
ここまでを L9e の完了条件とする。

## 14. 検証と保存

保存単位ごとに対象の `lake build` を実行する。
保存単位ごとに専用の公理監査を実行する。
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`sorryAx` を拒否する。
追加公理を拒否する。
HT-KQ への依存を認めない。
監査は公開定理だけでなく本レーンの全宣言を対象とする。
検証シェルでは `set -o pipefail` を指定する。
パイプを通したログの見かけの成功に依存しない。
工程完了時だけ全体ビルドを行う。
`git diff --check` を行う。
コミットは自分の検証済みファイルだけ。
`git commit --only` を使う。
ルートの既存変更を巻き込まない。
amend・rebase・reset を使わない。

## 15. 現在地

| 工程 | 状態 | 残る証明 |
| --- | --- | --- |
| 計画 | 作成 | 実装と同期する |
| L9a | 部分実装・対象ビルド済み | 可換性、零次数、相対ホモトピーとの比較、不変性 |
| L9b | 未着手 | fiber の連結射と完全性 |
| L9c | 設計確認点あり | 特定の Hom 極限の Kan 性 |
| L9d | 未着手 | telescope と π_* の計算 |
| L9e | 未着手 | Tot、hG、有理自明作用の比較 |

## 16. 主要宣言

以下は検証済みの宣言だけを記載する。
名前の共通接頭辞は `SerrePositivity.KST.Spectra`。
全て `SerrePositivity/KST/Spectra/HomotopyGroups.lean` に置く。

| 宣言 | 内容 |
| --- | --- |
| `simplexRel` | 最後の面の単位積による関係 |
| `simplexSetoid` | Kan 性から同値関係を実証 |
| `shiftRelStruct` | 隣接する面の関係を前へ移す |
| `unshiftRelStruct` | 隣接する面の関係を後ろへ移す |
| `nonempty_relStruct_iff_zero` | RelStruct の存在の面添字独立性 |
| `simplexRel_iff_relStruct` | 商の関係と任意の RelStruct の比較 |
| `KanHomotopyGroup` | 次数 n + 1 のホモトピー類の商 |
| `KanHomotopyGroup.mk_eq_iff` | 商の等式と充填関係の同値 |
| `KanHomotopyGroup.sound` | 任意の RelStruct を類の等式へ送る |
| `KanHomotopyGroup.mul_unique` | 積の充填の類の一意性 |
| `KanHomotopyGroup.mul_congr_left` | 左代表の独立性 |
| `KanHomotopyGroup.mul_congr_right` | 右代表の独立性 |
| `KanHomotopyGroup.mul_eq` | 指定した充填による積の計算 |
| `KanHomotopyGroup.exists_left_inverse` | 外側ホーンによる左逆元 |
| `KanHomotopyGroup.instGroup` | 商の群構造 |
| `mapSimplex` | 基点を保つ後合成 |
| `mapRelStruct` | 関係の充填の後合成 |
| `mapMulStruct` | 積の充填の後合成 |
| `KanHomotopyGroup.map` | 誘導群準同型 |
| `KanHomotopyGroup.map_id` | 恒等射の保存 |
| `KanHomotopyGroup.map_comp` | 合成の保存 |

検証コマンド：

```sh
set -o pipefail
lake build SerrePositivity.KST.Spectra
lake env lean scripts/audit_kst_spectra.lean
```

結果：対象ビルド成功。監査は私有宣言を含め 63 宣言、標準三公理のみ。
全体ビルドは L9a 完了時に行う。
ルートには指定の public import 一行を追加済み。
ルートは他レーンの未コミット変更を含むので、この保存ではコミット対象から外す。

## 17. 公開時の注意

工程の部分成果を全工程の完了として報告しない。
構造の定義だけを存在証明として報告しない。
入力された法則を証明したと報告しない。
有理化は実際の π_* の計算まで必要。
局所 Kan 性は γ1 の実質的な適用条件である。
π_* の長完全列は実際の連結射を伴う。
共有 import の破損時は依存箇所とエラーを報告する。
設計変更の提案時は変更箇所と理由を明記する。
通常の工程報告後は承認を待たず次の工程へ進む。

## 18. L9c の設計変更提案（未採用）

現行指定は維持している。以下は提案であり、Lean の定義にはまだ採用していない。
L9a の正次数の群構造はどちらの選択にも依存しない。

確認した原典：

- [HA](https://www.math.ias.edu/~lurie/papers/HA.pdf) Definition 1.4.2.8 と
  Proposition 1.4.3.6 の証明では、空間の列の構造は Ω への同値として扱う。
- [Kerodon の塔の補題](https://kerodon.net/tag/0194) Corollary 11.9.7.2
  （retired subsection の現行番号）は、逆極限の Kan 性に各遷移射の Kan fibration 性を使う。
- Mathlib `AnodyneExtensions/PushoutProduct.lean` の
  `fibration_pullbackObjObjπ` は、単射による源の制限に対する fibration 性を実証する。

現行の厳密 Hom の極限が非 Kan であると証明したわけではない。
未解決なのは、この特定の極限に対する充填の存在である。
段ごとの Hom の Kan 性だけからは一般の極限の Kan 性を導けない。
従って γ1 を適用するには、図式固有の補題が必要になる。

提案する変更箇所：

1. X_n ≅ ΩX_(n+1) の厳密同型を、π_* 同型となる構造写像で置き換える。
2. 源となるスペクトルの cell 分解を実際に構成する。
3. 有限段の写像空間を cell 分解の段への制限で作る。
4. 制限写像の Kan fibration 性を pushout-product の充填から証明する。
5. その逆極限を豊穣 Hom とし、合成・単位・局所 Kan 性を実証する。
6. coherent nerve と γ1 の利用、HT-KQ 不使用、γ3 まで ∞ 極限を主張しない方針は維持する。

この案でも cell 分解の存在と構造写像の同値性保存の証明は必要となる。
それを入力仮説に移さない。
ユーザーの決定前には L9c の対象や Hom を変更しない。
