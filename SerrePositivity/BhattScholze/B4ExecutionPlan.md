# B4：semiperfectoid環のperfectoid化の全射性

2026-10-14。計画段階。正本は`formalization-plans/bhatt-scholze.md`、
担当・待合せは`clmst.md` §0.2。B3の一般存在・普遍性は証明済み。
この計画の予定定理・予定ファイルは、実装済みの宣言ではない。

## 最終受渡し

p:ℕ、[Fact p.Prime]、R,S,C:Type u可換環、
hR:IsIntegralPerfectoid R p、q:R→S全射、
hS:DerivedCompletion.IsModuleComplete S (p:S) (ModuleCat.of S S)、
f:S→C、hf:IsPerfectoidization p fから、Function.Surjective fを証明する。
一般のpねじれ商・零環・任意イデアルを含める。
Sのp正則性、有界ねじれ、古典的完備性、有限生成性は最終入力に追加しない。

B3の具体的な構成射にも適用し、`IsPerfectoidization.surjective_iff`で
任意の普遍対象へ移送する。存在はB3を使い、B-I/B6の存在引用へ戻らない。
既存のpねじれのない古典的完備商のAPIは、一般定理と既存比較から証明する互換入口として保持する。
利用先・CLMST・共有ファイルの変更は共通担当へ渡す。

## 原典の確認と引用境界

著者公開版`paper/refs/BS-prisms-author.pdf`を参照する。
Thm 7.4はp.56で主張、証明はp.62。
Andréの平坦性補題はThm 7.14（p.61、arXiv v3では7.12）。
原典の全射性の順序は、任意イデアル→有限生成→単項、Andréによる根の存在、
根イデアル商のp完備化のperfectoid性、全射性である。
原典の「Andréにより仮定できる」の底変換・降下も証明する。

`Inputs/AndreFlatness.lean`の
`exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`は既存の名前付きsorry。
そこから得る根付き拡大と、その拡大を経由する全射性は条件付き成果と表示する。
その段階ではB-Sの引用解消・B4完成とは数えない。
新しいsorry・公理・外部引用は追加しない。

## 再利用できる成果と不足

| 項目 | 現状 | B4への接続 |
| --- | --- | --- |
| 一般B3存在・普遍性 | 証明済み | モデルの比較と標準射を使用 |
| perfectoid環の一般の被約性 | 共通`PerfectoidTorsionFrobenius`で証明済み | 根を消す任意perfectoid試験環に適用 |
| 根イデアル・冪等性 | `CompatibleRootIdeal`で証明済み | 単項根付きの場合の代数 |
| 根イデアル商・完備化の制限付き普遍性 | `CompatibleRootQuotient`で証明済み | 被約性とp完備性を供給して一般perfectoid試験環に適用 |
| 全射による前完備性の移送 | 共通`AdicCompleteness.isPrecomplete_of_surjective` | 完備化射の全射性に使用 |
| 普遍対象間の同型・核一致・全射性移送 | 共通`PerfectoidizationUniqueness` | 重複定義を作らない |
| 根イデアル商の完備化のperfectoid性 | 未実装 | B4aの中心 |
| 完備テンソルのperfectoid性・底変換比較 | 未実装 | B4b。BSの定理と共通導来基盤を分担 |
| 全射性の忠実平坦降下 | この適用形は未実装 | mod pの降下とadic全射判定を合成 |
| Andréの引用なしの必要部分 | 未実装・経路未確定 | B4cの成立性を先に確認 |

B3で証明したWitt比較射の全射性は、S→S_perfdの全射性とは別である。
B3の実H⁰の普遍性だけから構成射の全射性を推論しない。

## 工程とコミット単位

### B4-1：根付き商への普遍性接続

予定ファイル：`CompatibleRootPerfectoidUniversal.lean`。
R perfectoid、ρ:ℕ→R、ρ(n+1)^p=ρ(n)、K=compatibleRootIdeal ρ。
既存の`CompatibleRootCompletion p ρ`と具体的標準射をそのまま使用する。
任意perfectoid Tの被約性・p進完備性を供給して一意延長を証明する。
零Tを別枝で処理し、MathlibのFontaine非可逆性を零環へ要求しない。
この時点では候補のperfectoid性を仮定した条件付きIsPerfectoidizationと区別する。
André・B-S・B-Iはimportしない。

### B4-2：根イデアル商の完備化射の全射性

予定ファイル：`CompatibleRootCompletionSurjective.lean`。
Rのp進完備性からR/Kの前完備性を既存全射移送で供給し、
AdicCompletionへの標準射の全射性を得る。
合成R→R/(ρ₀)→CompatibleRootCompletion p ρの全射性を公開する。
Kの閉性・R/Kの分離性・有限生成性を暗黙に仮定しない。
古典的完備化への射を扱う工程であり、実導来完備化との同一視はまだ行わない。

### B4-3：根付き単項商の候補のperfectoid性

予定ファイル：`CompatibleRootCompletionPerfectoid.lean`。
上記候補が既存IsIntegralPerfectoidを満たすことを証明する。
B3の完全prism/Witt表示を再利用し、根の係数側の商を具体化する。
根で生成されるFrobenius安定イデアル、完全係数商、distinguished元の像、
実PD完備化後の商との比較を順に確認する。
compatible rootsをTeichmüller元へ移す際のuntilt図式も証明する。
古典的候補と実H⁰からの候補を同一視する場合は、標準射を両立させる比較同型を証明する。

B4-1〜2と合わせて、ρ₀の商からの具体的全射perfectoid化を公開する。
単項商R/(ρ₀)の導来p完備性は自動とはしない。
B3の未完備全射商の存在入口は利用できるが、それだけで全射性を結論しない。

### B4-4：一般イデアルへの拡張条件

原典どおり有限生成イデアル・単項への帰着を実装する場合、
未完備商の有向系、導来p完備化した余極限、perfectoid化との比較、
元の等式の有限段での検出を証明する。有限段の完備性を仮定しない。

別候補は、ρ:σ→ℕ→R（σ:Type u）の根族全体による商を直接扱う経路。
André拡大では全元に根があるため、任意Jの全元をσとして使える。
これが全一般性で証明できれば有限生成への帰着を省ける。
ただし単項結果から無条件には拡張せず、候補のperfectoid性と普遍性を確認してから採用する。
B4-3の証明後にこの選択を確定し、主計画へ記録する。

### B4-5：底変換と全射性の降下

予定ファイル：`PerfectoidCompletedTensor.lean`、`PerfectoidizationBaseChange.lean`、
`PerfectoidizationSurjectivityDescent.lean`。
BS著者版Lemma 10.3と完全標数p環のTor独立性を必要な環レベルで証明する。
完備テンソルのTor・完備化・mod p比較は既存共通基盤を使う。
一般の完備化対象や忠実平坦性の同等定義をBS内に作らない。

R→R'をperfectoid環へのp完全忠実平坦な射とする。
S'=R'/J R'（必要な導来完備化を明示）、CのR'への完備底変換Dを構成し、
S'のperfectoid化との標準射を両立させる比較を証明する。
Dのperfectoid性を先に証明し、形式的普遍性だけで仮定しない。

底変換後の全射性からmod pの余核を忠実平坦性で消し、
Sの前完備性とCのp分離性から既存adic全射判定でfの全射性を得る。
p完全忠実平坦性を通常の忠実平坦性と同一視しない。
B5のイデアル冪等性・B-S引用をこの証明に使わず、循環を避ける。

### B4-6：Andréの必要部分と条件付き合流

まず引用なしの入力型を固定する：R perfectoid、元族a:σ→Rに対し、
R' perfectoid、Algebra R R'、IsCompletelyFaithfullyFlat (span{p}) R'、
各a_sの像の両立するp冪根ρ_sを持つ拡大。
単項帰着が証明できる場合はσ=PUnitの入力でもよい。

既存André引用と`IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots`から
この入力を供給する補題は、独立した条件付きモジュールに置く。
純粋なB4a/B4bの監査へこのimportを混ぜない。
条件付き全射性の依存が既存Andréだけであることを監査する。

引用なしの候補経路は主計画§5の必要なroot-adjoining envelopeに限定する。
正則性、pd包の平坦性、mod pの忠実性、実完備化・完全化による保存を個別に検証する。
導来prismatic cohomology・Hodge–Tate比較・∞圏全体の新規構築へ拡大しない。
成立性が未確認の古典的計算を証明済み入力として採用しない。

### B4-7：一般全射性と既存B-S入口の解消

引用なしの根付き拡大、一般イデアルへの拡張、底変換比較と降下がすべて揃った後、
最終受渡し型を証明し、B3の具体的射と任意IsPerfectoidizationに適用する。
`Inputs/SemiperfectoidSurjectivity.lean`の既存sorryを同じ署名の証明へ置き換える。
既存公開APIを削除・弱化せず、利用先の接続は共通担当に渡す。
André依存が残っていれば、この工程は未完了として報告する。

## 共通基盤への要求（主計画§8にも記録）

### G1：mod p忠実平坦降下とadic全射判定の接続

R,S,C,R':Type u可換環、Algebra R S/C/R'、f:S→ₐ[R]C、
Sはspan{p}に関して前完備、Cはspan{p}に関して分離とする。
R/p上の(R/p)⊗[R]R'が忠実平坦で、f mod pをこの加群にテンソルした写像が全射なら、
Function.Surjective fを得る。通常のR'の忠実平坦性は要求しない。
利用：B4-5。既存adic判定とModule.FaithfullyFlatを再利用する適用形。
不足：この合成の公開入口は未確認。既存APIで直接合成できれば要求を閉じる。
待つ工程：一般降下だけ。B4-1〜3、根族代数、BSのTor計算は独立に進める。

### G2：実導来完備テンソルの環・mod p比較

R,S,T:Type u可換環とR-代数構造について、既存derivedTensor R S Tの
実p導来完備化のH⁰、環構造・標準射・S/Tの射との図式を必要とする。
高次ホモロジーの消滅やperfectoid性はこの要求の結論に含めず、BS側が証明する。
B=S⊗[R]T、Cp=PDCompletionH0 B p (0:B)を比較先の具体的候補とする。
K=(derivedTensor R S T)の実p導来完備化がIsConcentratedInDegreeZeroを満たすとき、
H⁰(K)≃Cpの環同型と標準単位の両立を必要とする。
mod p比較では、SがIsCompletelyFlat (span{p:R})を満たす場合、
K⊗^L_R R/pと(S/p)⊗^L_(R/p)(T/p)の比較を供給する。
右辺も離散であるとBS側が証明した後、環レベルのmod p比較へ移す。
実際の型は共通側の完備化APIを再利用し、PDCompletionH0(-,p,0)の利用可否も確認する。
無条件の古典的完備化との同一視・離散性は要求しない。
利用：B4-5の底変換。既存PD完備化は環の入力を持つが、derivedTensorの一般複体の
完備化・環・mod p比較をそのまま供給する入口は未確認。
待つ工程：完備底変換の図式だけ。B4a、Tor独立性、候補根付き拡大の計算は続ける。

## 最初に実行する単位と検証

最初はB4-1、次にB4-2。ここまでは共通待合せ・André引用なしで進める。
その後B4-3の候補のperfectoid性を優先し、並行して必要な底変換の型を調査する。
調査だけで終了せず、型を確定した公開補題を実装する。
各単位で対象ビルド、BS専用assert_no_sorry・公理依存・import閉包を監査し、
検証済みの自分の変更だけを個別コミットする。
純粋成果、既存Andréに相対的な成果、未実装を別に報告する。
B-I/B6は引用のまま維持し、他チャットへのメッセージは送らない。

## B4-1実装完了（2026-10-14）

`CompatibleRootPerfectoidUniversal.lean`で、任意perfectoid試験環への唯一延長、
候補のperfectoid性を明示仮定したIsPerfectoidization、任意普遍対象との比較同型を公開。
零試験環も一般の被約性・完備性APIで処理した。3公開定理の対象ビルドと
専用監査`scripts/audit_bhatt_scholze_b4.lean`が成功。標準3公理のみ。
候補のperfectoid性は未結論であり、B4の全射性の完成とは区別する。

共通の一般被約性のモジュールは、推移的importで既存B-Iの入力モジュールも
読み込むが、再利用したisReducedとこの3定理の証明依存にはsorryAxがない。
import閉包と実際の証明依存を区別して監査する。共通ファイルは編集しない。

## B4-2実装完了（2026-10-14）

`CompatibleRootCompletionSurjective.lean`で、p前完備な基底の根イデアル商の
自身のp作用に関する前完備性、完備化への標準射の全射性、
最初の元の商からの具体的な標準射の全射性を証明した。
商の分離性・根イデアルの閉性・有限生成性は不要。
候補のperfectoid性を明示仮定した場合の任意IsPerfectoidizationの全射性も、
既存surjective_iffで移送した。候補のperfectoid性はまだ未証明。

4公開定理の対象ビルド（3280ジョブ）とB4専用監査が成功。標準3公理のみ。
B4-1〜2の7公開定理はAndré・B-S・B-Iの証明依存を持たない。
次はtilt側の根イデアル商の完全性と、実PD完備化との商比較を進める。
