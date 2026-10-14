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
単位derivedTensor→Bのaugmentationの錐の実p完備化が消える等、
比較を保証する条件を証明した場合に、H⁰(K)≃Cpと標準単位の両立を要求する。
完備化後のKの離散性だけからこの同型を推論しない。

mod pでは常に成立する導来比較
(S⊗^L_R T)⊗^L_R R/p ≃ (S⊗^L_R R/p)⊗^L_(R/p)(T⊗^L_R R/p)
を使う。通常のS/p、T/pへ置き換える場合は、両側の導来剰余の離散性を供給する。
Sの完全平坦性だけではT側のTor消滅は出ない。共通計画§9.7dの反例と修正を確認した。
原典Lemma 10.3のprism側ではA,B,Cがp正則であるため、この条件をBS側から供給できる。
元のperfectoid環自体のp正則性を一般入力に追加しない。
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

## B4-3／B4a実装完了（2026-10-14）

`CompatibleRootPerfectQuotient`で完全標数p環の根イデアル商の完全性を証明。
商のCharPを仮定せず、零環の商を含む。
`CompatibleRootTilt`で根列の全座標、両立性、untilt復元、
根を消す射がtilt根イデアルを消すこと、tilt根イデアル商の完全性を公開した。

`CompatibleRootPDComparison`で、具体的な全射Witt型商と完備化の図式を仮定した
古典的根商のp完備化と実PD完備化商の比較同型を証明。標準射を両立させた。
実完備化の環普遍性と、完備化候補への標準射の全射性から両逆写像を検証する。
古典的完備化への無条件の置換はしない。

`CompatibleRootCompletionPerfectoid`でこれらを実際のperfectoid Rのtiltへ適用し、
任意の両立する根列ρについてCompatibleRootCompletion p ρの
IsIntegralPerfectoidを証明した。一般のpねじれと零環も含む。
具体的なcompatibleRootCompletionMapのIsPerfectoidizationと、
任意の普遍perfectoid化の全射性まで、候補のperfectoid性の仮定を解消した。
R/(ρ₀)の導来完備性を追加していない。André・B-S・B-I・B5の引用を使わない。

新規13公開宣言の対象ビルド、B4専用監査、全体ビルド4456ジョブが成功。
すべての公理依存はpropext・Classical.choice・Quot.soundのみ。
現在の4モジュールのimport閉包205モジュールにInputs・CLMST・Paper・RootTowerなし。
B4-1時点の共通importの引用混入は、その後の共通側の抽出で解消している。
共有ファイルはBS側では編集していない。

一般B4は未完了。任意イデアルへの拡張、底変換・全射性の降下、
引用なしの必要な根付き拡大は残る。既存Andréのsorryを使う合流は条件付きと区別する。
次は任意根族のイデアル・tilt商・普遍性を直接扱う経路を検証し、
有限生成帰着を省けるかを証明によって確認する。

## B4-4前半：任意根族の代数と普遍性（2026-10-14）

`CompatibleRootFamilyIdeal`でσ:Type uの任意根族の最初の元のイデアルと
全段の根イデアルを定義。包含・被約環への射による消滅・冪等性・
完全標数p環のFrobenius不変性・係数商の完全性を証明した。
`CompatibleRootFamilyQuotient`で、最初の元の商から全根族のp完備化への
具体的射、任意perfectoid試験環への一意延長、前完備性、標準射の全射性を公開。
候補のperfectoid性を仮定したIsPerfectoidizationも明示した。

14公開宣言の対象ビルドとB4専用監査が成功。標準3公理のみ。
有限生成性は仮定せず、空の根族も型の範囲内。
一般根族の候補のperfectoid性はまだ未証明であり、この前半をB4-4全体の
完成とは数えない。単項で証明した実PD商比較の共通部分を抽出し、
一般根族へ同じ証明を渡す。既存の一般定義や共通補題を重複させない。

## B4-4完了：任意根族・任意根付きイデアル（2026-10-14）

`PerfectDeltaPDQuotientComparison`へ単項と根族の商比較の共通証明を抽出した。
`CompatibleRootPDComparison`の既存署名を保ったまま、その証明を共通部分へ置換。
単項結果も再ビルド・B4全宣言監査で再検証した。
`CompatibleRootFamilyPDComparison`で任意根族の具体的完備化と実PD商の比較を証明。
`CompatibleRootFamilyCompletionPerfectoid`で任意σ:Type uについて候補の
IsIntegralPerfectoid、標準射のIsPerfectoidization、任意普遍対象の全射性を証明した。
一般pねじれ、零環、空の根族を含み、有限生成性は不要。

`RootedIdealSurjectivity`で、任意イデアルJの全元が両立する根を持つ場合の
`surjective_of_isPerfectoidization_of_rootedIdeal`を公開。
商のp正則性・完備性・イデアルの有限生成性を追加しない。
これで任意根族を直接扱う経路が全一般性で証明できたため、この経路を採用する。
B4の一般イデアルへの帰着のための有限生成化・単項への帰納・
そのための完備有向余極限比較は不要になった。
ただし根付き拡大を元のRへ降下するB4-5と、引用なしのB4cは未完了。

新規8公開宣言と単項比較の再利用の監査が成功。対象ビルド3288ジョブ、
全体ビルド4466ジョブ成功。すべての公理依存は標準3公理のみ。
André・B-S・B-I・B5の証明依存はない。共有ファイルは編集していない。

G1は共通計画§9.7cでG1-1〜4の公開・監査まで完了したことを確認。
`PrincipalAdicFaithfulDescent.surjective_algHom_of_principal_residue_baseChange`が
要求した環商の署名を供給する。BS側は再監査・適用し、同等の一般降下補題を作らない。
G2の完備テンソル比較とBS側のperfectoid性・Tor計算は別に残る。

## B4-6の条件付き入力（2026-10-14）

`AndreCompatibleRootsConditional.lean`で既存André入力から、任意σ:Type uの元族について
p完全忠実平坦なperfectoid拡大とその像の両立するp冪根を選ぶ補題を公開した。
絶対整閉からの根列の選択は既存の証明済み一般補題を使う。
新しいsorry・公理・外部引用は追加していない。

この補題の依存には既存
`Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`のsorryAxが残る。
専用`scripts/audit_bhatt_scholze_andre_conditional.lean`でその名前付き境界を確認した。
純粋なB4監査にはこのimportを混ぜない。これは条件付き入力だけであり、
引用なしのB4c・一般B4の全射性・B-S引用の解消は未完了。

## B4-5前半：G1接続と根イデアルの平坦性（2026-10-14）

`PerfectoidizationSurjectivityDescent`で受領G1をそのまま使い、
導来p完備なSのperfectoid化f:S→ₐ[R]Cとp完全忠実平坦なR'について、
f mod pの(R/p)⊗[R]R'へのテンソル射の全射性からfの全射性を証明した。
Sの前完備性は既存の導来完備性の漸化式判定から供給し、Cの分離性は
既存IsIntegralPerfectoidから供給する。通常のR'の忠実平坦性と混同しない。
一般の降下判定を重複実装しない。完備底変換との比較はこの定理に仮定しないが、
その比較を使ってテンソル射の全射性を供給する工程は別に残る。

`CompatibleRootIdealFlat`で、被約環の両立する根のイデアルが平坦であることを
Mathlibの方程式判定から直接証明。一段後の根と遷移係数が前段の乗法核を
消す計算も公開した。p正則性・Noether性・標数pを要求しない。
BS17著者版Lemma 3.16（Witt.pdf、印刷p.13）の根イデアルの計算を確認し、
引用せずにLean証明した。Tor独立性全体や完備テンソルのperfectoid性とは区別する。

4新規公開定理の対象ビルド、B4全宣言監査、全体4466ジョブのビルドが成功。
公理は標準3公理のみ。根付きイデアルのテンソルの単射性、一般Tor独立性、
完備底変換の比較、引用なしの根付き拡大は引き続き残る。

## B4-5：根イデアル商のTor独立性（2026-10-14）

`CompatibleRootIdealTensor`で、根イデアルのテンソルの任意の元を一段の根の
純粋テンソルで表示し、被約終域への標準射の単射性を証明した。
終域の正則性・平坦性は不要。
`CompatibleRootQuotientTor`で、既存のTor長完全列・零次の自然性と
根イデアルの平坦性を合成し、根イデアル商と被約なR-代数Cの
正次数のTorModuleのSubsingleton、既存derivedTensorの次数0への集中を証明。
被約性と根の両立性を明示し、標数p・Noether性・正則性を課さない。

7公開宣言の対象ビルドとB4専用監査が成功。標準3公理のみ。
全体ビルド4490ジョブ成功。一般の完全環のTor独立性へ拡張する工程は残る。
BS17著者版Lemma 3.16の直接証明と同じ根イデアルの部分を引用なしで形式化した。

G2の元要求の不十分な仮定を共通側の計画§9.7dで確認し、上の要求を修正した。
通常の商への置換に必要な両側のTor条件を黙って追加しない。
Witt係数のテンソルとdistinguished商からカテゴリー上のperfectoid余積を直接構成する
候補も調べるが、普遍性・標準射・mod p比較をすべて証明するまでB4の経路として採用しない。
一般B4、引用なしの根付き拡大、B-S引用の解消は引き続き未完了。

## B4-5：Witt係数テンソルと生成元の準備（2026-10-14）

`WittDistinguishedQuotientPerfectoid`で、完全標数p係数環kの任意のdistinguished
Witt元dについてW(k)/(d)のperfectoid性を証明した。
台W(k)のd完備性の仮定を追加しない。F5による標準商のp完備性と
実PD完備化後の商の比較同型を使い、零環の商・一般pねじれ商も含む。
標準Fontaine比較射の同型のd完備性の仮定まで消したという主張ではない。

`PerfectCoefficientTensor`で、完全標数p環の係数テンソルK=A⊗[R]Bの
完全性を、逆Frobeniusの具体的な環射から証明。Kが零環の場合も含む。
基底の逆Frobeniusを通じて一致する両因子の環射をMathlibのAlgHom版の
テンソル普遍性へ接続するBS専用RingHom入口も公開した。
終域の既存R-代数構造を入力に課さないため、通常のR線形なmapではない
逆Frobeniusと、今後の係数余積の環射に利用する。
新しいテンソル・完備性の定義を作らず、Mathlibの対象と普遍射を再利用する。

`FontaineKernelNaturality`で、源のFontaine核内のdistinguished元dの
標準Witt像が、単項な終域のFontaine核を生成することを証明。
既存核判定・Wittのδ自然性・Fontaineの自然性を使う。環のp正則性は不要。
これにより、同じ源の生成元で複数のperfectoid商を表示する準備ができた。

7新規公開宣言の対象ビルドとB4全宣言監査が成功。標準3公理のみ。
全体ビルド4495ジョブ成功。一般B4・B-S解消はまだ未完了。

### 次の独立工程：Witt表示による余積候補

予定BSファイル：`PerfectoidWittBasePresentation.lean`、`PerfectoidWittPushout.lean`、
`PerfectoidWittPushoutModP.lean`、`PerfectoidizationBaseChange.lean`。
R,S,T perfectoidとS←R→Tを入力とし、係数環
K=S♭⊗[R♭]T♭と、Rのdistinguished Fontaine核生成元の像ξを用いる。
非零Kの候補はW(K)/(ξ)。K=0および零環の因子は別枝で扱う。
上の一般Witt商の結果はこの候補のperfectoid性を供給するが、
余積の普遍性・S/Tからの標準射・原環のテンソルからの写像・mod p比較は未証明。

最初は源の生成元を用いたS/TのWitt商表示と標準射の両立を公開する。
次に候補の全perfectoid試験環への普遍性と、通常テンソルのmod pとの比較を証明する。
その後、B3のperfectoid化をこの候補へ底変換する図式とG1の実入力を接続する。
すべての図式・零環の枝・一般pねじれ入力を証明するまで、この経路を採用しない。
カテゴリー上の余積や通常のmod p比較を、実導来完備テンソルとの同型と同一視しない。
G2の導来比較と一般Tor独立性は引き続き別に必要な工程として記録する。
引用なしの必要な根付き拡大も未完了であり、André条件付き入力からの成果で
一般B4の完成を宣言しない。

## B4-5：源の生成元によるWitt商表示（2026-10-14）

`PerfectoidWittBasePresentation`で、源のdistinguished Fontaine核元の像を
生成元とする終域の具体的なWitt商同型を構成し、標準商射とFontaine写像、
逆射との合成図式を証明した。p正則性は要求しない。
非単元p・p完備性・mod p Frobenius全射性・Fontaine核の単項性を明示した
3公開宣言を対象ビルドとB4専用監査で検証する。
余積の構成・普遍性・mod p比較は次工程。一般B4の全射性は未完了。

## B4-5：係数Witt余積の完備試験環への普遍性（2026-10-14）

BS専用`WittCoefficientPushout.lean`を追加。既存の
`existsUnique_wittResidueLift_of_complete`と`wittLift_unique`を使い、
完全標数p環A←R→Bの両立するWitt射をW(A⊗[R]B)から任意の
p完備環Dへ一意に延長することを証明した。終域のp正則性・非零性は不要。
係数テンソルが零環になる場合は剰余環D/pが零環になり、p完備性から
Dが零環になることを既存APIで示して処理。K自体のCharPを仮定する
入口と、零環Kも含む完全係数の入口を分けて公開した。
基底Witt射の一致と、p Hausdorff終域への射の忠実性も証明した。
4公開宣言を対象ビルドとB4専用監査で検証。
これはまだdistinguished商の余積ではなく、商への降下とmod p比較が残る。

## B4-5：共通distinguished元によるWitt商の余積（2026-10-14）

`PerfectoidWittPushout`に、共通基底Witt元dの像による具体的な商
`WittCoefficientPushout p R A B d`と左右の標準射を定義。
標準射の代表元の式、基底Witt環上の一致を証明した。
dがdistinguishedなら候補はperfectoidであり、係数テンソルが零環になる場合も含む。
任意のp完備環Dへの、両因子の商からの両立する射の一意な延長を証明。
試験環のp正則性・非零性は不要。普遍性自体にはdのdistinguished性も不要。

8公開宣言を対象ビルドとB4専用監査で検証する。
これは具体的な係数Witt商の余積であり、一般perfectoid環のFontaine商表示との
接続・原環のテンソルからの標準射・mod p図式は引き続き残る。
導来完備テンソルとの比較を主張せず、一般B4の全射性を完成とは数えない。
