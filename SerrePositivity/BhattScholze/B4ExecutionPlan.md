# B4：semiperfectoid環のperfectoid化の全射性

2026-10-15。実装中。正本は`formalization-plans/bhatt-scholze.md`、
担当・待合せは`clmst.md` §0.2。B3の一般存在・普遍性は証明済み。
各工程の当初予定と、後半の実装記録を区別する。
B4-1〜4とB4-5の根付き拡大データに相対的な降下は証明済み。
一般B4の引用なし完成にはB4-6の必要な根付き拡大の存在が残る。
Witt通常余積による現在の降下経路は、後半の2026-10-15の記録を参照する。

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
| 根イデアル商の完備化のperfectoid性 | 単項・任意根族で証明済み | B4aに使用 |
| 底変換候補のperfectoid性・標準mod p比較 | Witt通常余積経路で証明済み | B4bの現在の降下経路。導来比較は別工程 |
| 全射性の忠実平坦降下 | 根付き拡大データを明示して証明済み | G1と既存adic全射判定を合成 |
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

## B4-5：Witt表示を入力する通常テンソルのperfectoid化（2026-10-14）

BS専用`WittPresentedPerfectoidTensor.lean`を追加。
共通distinguished元の像を使うS,TのWitt商表示、全射な基底Witt写像θ、
θとR→S/Tとの合成図式を明示して入力する公開定理
`exists_wittPresentedTensorPerfectoidization`を証明。
S⊗[R]Tから具体的なWitt係数余積への射Fを構成し、左右の標準射の図式と
`IsPerfectoidization p F`を証明した。係数テンソルが零環になる場合も含む。
これは通常テンソルに関する普遍perfectoid化であり、導来テンソルとの同型を
仮定・主張しない。Fontaine表示を実際のperfectoid入力から供給する工程と
mod p比較、降下、引用なしの根付き拡大は残る。
対象ビルドとB4専用監査で検証する。

## B4-5：任意perfectoid入力からの係数余積の実供給（2026-10-14）

BS専用`PerfectoidTensorPerfectoidization.lean`を追加。
`exists_perfectoidTensorPerfectoidization`は、任意のperfectoid環R,S,Tと
R-代数構造を入力し、具体的な環E・CommRing構造・F:S⊗[R]T→Eと
`IsPerfectoidization p F`を存在結論として証明する。
通常テンソルが零環の場合は恒等射、それ以外は各環の非零枝から
標準Fontaine表示を供給して、上の具体的Witt係数余積を使う。
有限性・p正則性・基底や因子の非零性を仮定しない。
源の生成元による商表示とFontaine自然性の図式を実際に供給し、
抽象な表示データを未証明の仮定として残していない。

対象ビルドとB4専用監査で検証。
通常テンソルのmod pとの比較・その自然な図式・G1への接続・
引用なしの根付き拡大は残る。導来テンソルとの比較は別工程。
全体ビルドはWitt商余積まで4498ジョブ成功、引用依存のない公開宣言は標準3公理のみ。

## B4-5：係数余積のmod p同型と左右の式（2026-10-14）

`PerfectoidWittPushoutModP`で、K=A⊗[R]BにCharP pを持つ枝の
具体的同型E/p≃K/(image(d₀))と、Witt代表元・左右の標準射の式を証明した。
既存の`wittQuotientModPEquiv`を再利用し、新しい剰余商の定義を作らない。
4公開宣言を対象ビルドとB4専用監査で検証。
零環Kの枝も含むperfectoid化の存在は前工程で証明済みだが、
このmod p同型の入口ではCharP K pを明示する。
次にK/(image(d₀))と両因子の剰余商のテンソルを同定し、
実perfectoid入力の通常テンソルのmod pと、G1用の自然な図式を接続する。
この式だけで全mod p比較の完成とはしない。

最新検証：全体4508ジョブのビルド成功。新規公開宣言はB4専用
`assert_no_sorry`と公理表示で標準3公理のみ。今回の新規モジュールの
プロジェクト内import閉包158件にInputs・CLMST・Paper・RootTowerなし。
全体ビルド中の既存Inputsのsorry警告は、これら新定理の依存ではない。

追加の次工程候補：Witt商余積の普遍性は全p完備試験環に成立するため、
表示付き通常テンソルの定理をその普遍性まで強め、pが零の試験環を使って
標準射のmod p同型を直接証明する。この比較が実証明できれば、
係数商テンソルの多段同型を介さずG1用の通常mod p図式へ接続できる。
導来テンソルとの比較の代用とはせず、証明後にB4用の経路として判定する。

## B4-5：表示付き通常テンソルの全p完備試験環への普遍性（2026-10-14）

`WittPresentedPerfectoidTensor`を証明の複製なしに整理し、
`exists_wittPresentedTensorCompletion`として、具体的なperfectoid候補へのFが
任意のp完備環Dへの射を一意に経由することを公開した。
既存の`exists_wittPresentedTensorPerfectoidization`の型は保持し、
一般perfectoid試験環のp完備性を供給する系とした。対象ビルド成功。
BS専用の次ファイル`WittPresentedPerfectoidTensorModP.lean`で、
この普遍性から標準mod p射の全単射性を直接証明する。
通常完備化の普遍性についての証明であり、導来完備テンソルと
古典的完備テンソルを比較せずに同一視する主張ではない。

## B4-5：標準mod p比較の直接証明（2026-10-15）

`WittPresentedPerfectoidTensorModP`で、全p完備試験環への普遍性から
標準mod p射の全単射性を証明した。源の剰余商A/pへ一意な逆射を
構成し、終域の剰余商E/pへの普遍性で逆射の両側の合成を証明。
p=0の試験環がp完備であることをMathlibのbot完備性から供給する。
一般完備性の定義やWitt持上げを重複しない。

`PerfectoidTensorPerfectoidization`を強め、
`exists_perfectoidTensorPerfectoidization_modP`として、任意perfectoid環
S←R→Tに対し、E・環構造・F:S⊗[R]T→E・IsPerfectoidizationと
標準`modPMap p F`の全単射性を同時に証明。
元の存在APIの型は保存して、この強い結果の系とした。
基底・因子・テンソルの零環の枝、一般pねじれ入力を含む。
これは通常テンソルと候補の実際の標準mod p射についての証明である。
実導来テンソルの比較とは同一視しない。

### B4降下への残る接続

この通常余積経路を、B4用の基底変更候補として進める。
G2の一般導来比較や完全環の一般Tor独立性は別工程として保持するが、
この標準mod p同型の証明にはその未実装部分を仮定しなかった。
次にf:S→Cの普遍perfectoid化をC⊗[R]R'の上記候補Eへ底変換し、
S⊗[R]R'→EのIsPerfectoidizationを証明する。
商R→Sの底変換と根付き商の全射性をつなぎ、通常テンソルの剰余商の
標準同型を通してG1の剰余テンソル射の全射性を供給する。
G1による元のfの全射性の降下、引用なしの必要な根付き拡大は未完了。
既存André入力からの降下が完成しても条件付きであり、B-S引用解消には数えない。

最新検証：標準mod p比較まで対象ビルド・B4専用監査成功。
全体4510ジョブ成功。新規2公開定理と既存APIの再検証は標準3公理のみ。
プロジェクト内import閉包159件にInputs・CLMST・Paper・RootTowerなし。

## B4-5：B3の普遍性の通常テンソルによる基底変更（2026-10-15）

`PerfectoidizationBaseChange`で、f:S→ₐ[R]Cのperfectoid化と、
F:C⊗[R]T→Eのperfectoid化から、具体的な合成
F∘(f⊗id):S⊗[R]T→EのIsPerfectoidizationを証明。
この形式的な普遍性の補題にはR,S,Tのperfectoid性や完備性を仮定しない。
共通基底上での一致はfのAlgHom性と元の普遍性から証明した。
新しいperfectoid化の定義や一意性の重複実装はない。

`exists_perfectoidizationTensorBaseChange`では、任意perfectoid基底R、
任意perfectoid R-代数Tと任意のf:S→ₐ[R]CのIsPerfectoidizationを入力し、
具体的E・環構造・F・IsPerfectoidization p F・標準mod p全単射性・
上記合成射のIsPerfectoidizationを同時に結論する。
有限性・p正則性・非零性は不要。S自体の完備性もこの定理に仮定しない。
3公開宣言の対象ビルドとB4専用監査を行う。
残件は全射商の通常底変換と根付き商の全射性の接続、G1の剰余テンソル図式、
引用なしの必要な根付き拡大。一般B4の全射性・B-S引用解消は未完了。

基底変更までの最新検証：対象3235ジョブ、B4専用全公開宣言監査、
全体4512ジョブ成功。新定理は標準3公理のみでsorry依存なし。
新規モジュールのプロジェクト内import閉包160件に
Inputs・CLMST・Paper・RootTowerなし。

## B4-5：根を持つ実際の核への接続（2026-10-15）

予定BS専用モジュール`RootedKernelSurjectivity.lean`、
`RootedTensorBaseChangeSurjectivity.lean`をこの工程で追加する。
前者で、任意の全射q:R→Sの実際の核の各元が両立する根を持つ場合の
任意IsPerfectoidization f:S→Cの全射性を証明した。
qの標準核商同型を使い、既存の根付きイデアル商の全射性へ接続する。
商の完備性・p正則性・有限生成性は不要。対象ビルド3289ジョブ成功。
B4専用公開宣言監査を行い、次に通常テンソルの標準全射へ適用する。
核の根を供給する工程はこの定理に仮定として残り、一般B4の全射性とは区別する。

## B4-5：根付き通常底変換後の全射性とmod p全射性（2026-10-15）

`RootedTensorBaseChangeSurjectivity`で、algebraMap R Sが全射なら
T→S⊗[R]Tが全射となるMathlib既存補題を使い、実際の核の根を入力して
F∘(f⊗id)の全射性を証明した。
Fの標準mod p射が全単射なら、通常テンソル射f⊗idのmod pが全射になることを
実際の標準商射の図式から証明。公開
`surjective_modP_tensorMap_of_rootedPerfectoidBaseChange`は、
任意perfectoid基底R・perfectoid拡大T・全射algebraMap R Sとfの
IsPerfectoidization、底変換した実際の核の根を入力し、
modPMap p (TensorProduct.map f id)の全射性を結論する。
具体的Witt余積の存在・普遍性・mod p比較は内部で既証明APIから供給する。
商の完備性・p正則性・有限生成性を要求しない。

3公開定理の対象ビルド3300ジョブ成功。B4専用監査を行う。
全射商の通常底変換と根付き商の接続はこの形で証明できた。
次はこの通常テンソルの標準mod p射をG1の正確な剰余テンソル線形射へ
移す自然な同型と図式を証明し、完全忠実平坦性で降下する。
核の根を供給する引用なしの必要な拡大も未完了。一般B4完成とは数えない。

## B4-5：G1の正確な剰余テンソル図式（2026-10-15）

予定BS専用`TensorResidueBaseChangeComparison.lean`と
`RootedPerfectoidSurjectivityDescent.lean`をこの工程で追加する。
前者でG1の既存`principalAdicQuotientAlgebra`をそのまま使い、
((R/p)⊗[R]T)⊗[R/p](S/(image p))≃(S⊗[R]T)/pを構成。
Mathlibの基底変更消去と商テンソル同型を合成し、純粋テンソルの代表元の式を証明。
比較同型がG1の`principalAdicReductionMap.lTensor`と
標準`modPMap p (TensorProduct.map f id)`を結ぶ自然性を証明し、
通常mod p全射性からG1の剰余テンソル線形射の全射性を供給する公開定理を証明。
導来テンソル、Tor、p正則性、完備性の仮定をこの通常比較に要求しない。

4公開宣言の対象2521ジョブ成功。B4専用監査を行う。
これによりG1の正確な剰余テンソル図式が証明できた。
次に根付き完全忠実平坦perfectoid拡大を入力する全射性降下を公開し、
引用なしのそのような拡大の存在を残件として切り分ける。

## B4-5：根付き完全忠実平坦拡大からの全射性降下（2026-10-15）

`RootedPerfectoidSurjectivityDescent`で、既証明の通常mod p全射性を
G1の正確な剰余テンソル射へ移し、既存の導来p完備からの前完備性と
完全忠実平坦降下を適用した。
公開`surjective_of_isPerfectoidization_of_rootedPerfectoidBaseChange`は、
任意perfectoid基底R・全射algebraMap R S・Sの実導来p完備性・
f:S→ₐ[R]CのIsPerfectoidization、perfectoidなp完全忠実平坦拡大Tと
T→S⊗[R]Tの実際の核の両立する根を入力し、fの全射性を結論する。
Tの全元の根を入力する版、およびIsAbsolutelyIntegrallyClosed Tから
既存の証明済み根の補題を使う版も公開した。拡大の存在は結論に含めない。
一般商とpねじれのない商を区別し、p正則性・有限性・古典的完備性を仮定しない。

3公開定理の対象3311ジョブ成功。B4専用引用なし監査を行う。
B4-5の降下の接続は、明示された拡大データに相対的に証明済みとなった。
B4-6の引用なしの必要な根付き完全忠実平坦perfectoid拡大の存在が主要残件。
既存André引用をこの入口に供給する一般形は、予定BS専用
`AndreSurjectivityConditional.lean`に分け、既存の条件付き監査だけで監査する。
これを一般B4の引用なし完成やB-S引用解消とは数えない。

## B4の一般全射性：既存André入力に相対的な接続（2026-10-15）

`AndreSurjectivityConditional`に、具体的q:R→S、f:S→Cと全射q、
RのIsIntegralPerfectoid、Sの実導来p完備性、fのIsPerfectoidizationを入力する
`surjective_of_isPerfectoidization_of_andre`を公開した。
既存Andréの名前付き引用で得たT・p完全忠実平坦性・perfectoid性・
IsAbsolutelyIntegrallyClosedを、上の証明済み降下定理へ供給した。
一般pねじれ商・零環を含み、有限性・p正則性・古典的完備性を課さない。
これは既存引用に相対的な途中成果であり、B4の引用なし完成ではない。
専用条件付き監査だけに加え、pure B4監査のimportには加えない。
既存のB-S引用や公開APIを先行して変更・削除しない。

### 引用なしの完成に必要な残件

任意perfectoid Rと全射商q:R→Sについて、perfectoid R-代数Tで
IsCompletelyFaithfullyFlat (span p) Tを満たし、
T→S⊗[R]Tの核の各元が両立するp冪根を持つ拡大を構成・証明すれば、
公開されたpure降下定理が一般B4を供給する。
全元が根を持つTやAICは十分条件であり、それ自体を必要条件としない。
元の核Jの生成元の像の根だけを構成する経路なら、
ker(T→S⊗[R]T)=J.map(algebraMap R T)と根付き生成族版への接続がさらに必要。
根付き拡大の古典候補・制限されたprismatic envelope候補は、
perfectoid性とp完全忠実平坦性を証明するまで成立・採用済みとはしない。
一般B4・B-S引用解消は未完了。

今回の最終検証：pure B4全公開宣言監査成功。根付き降下は標準3公理のみ。
条件付き監査は既存Andréの名前付きsorryだけが残ることを公理表示・sorry表示で確認。
全体4514ジョブ成功。pure降下のプロジェクト内import閉包230件に
Inputs・CLMST・Paper・RootTowerなし。
André入力の古い「未使用」記述を、実際の条件付き依存と残件を示す記述に更新した。

## B4-6：通常底変換核と元の生成族の像（2026-10-15）

予定BS専用`TensorBaseChangeKernel.lean`、`RootedPresentationSurjectivity.lean`、
`RootedFamilyPerfectoidSurjectivityDescent.lean`をこの工程で追加する。
前者で全射algebraMap R Sの核JをTへ拡張したイデアルが
T→S⊗[R]Tの実際の核であることを証明。
商T/JTへの普遍射をMathlibと既存BSテンソル射から構成し、両包含を証明した。
平坦性・完備性・有限生成性を要求しない通常底変換の核の計算である。
J=span(range a)なら、初項がalgebraMap R T (a s)の任意の族ρが
底変換核を初項イデアルとして生成することも証明した。
この核の同定自体では後続項が根である仮定は不要。
2公開宣言の対象ビルドとB4専用監査を行う。
次に生成族の根だけを入力する全射性降下へ接続する。
引用なしの根付き拡大の存在は引き続き未実装。

## B4-6：核の根付き生成族による全射商（2026-10-15）

`RootedPresentationSurjectivity`で、全射q:R→Sの核が
compatibleRootFamilyZeroIdeal ρと一致する場合、任意IsPerfectoidization f:S→Cが
全射であることを証明した。Rはperfectoid、ρは任意添字の両立する根族。
核の全元の根・拡大のAIC・有限生成性・商の完備性・p正則性は要求しない。
標準核商同型と既証明の根族商の全射性を使用する。
1公開定理の対象3288ジョブ成功。B4専用監査を行う。
次に元の核の生成族の像の根だけを入力する降下定理へ接続する。

## B4-6：元の核の生成族の根だけを要求する降下（2026-10-15）

`RootedFamilyPerfectoidSurjectivityDescent`で、任意生成族a:σ→R、
ker(algebraMap R S)=span(range a)と、各algebraMap R T(a s)を初項とする
両立する根族ρを入力し、底変換した合成射の全射性を証明した。
公開`surjective_of_isPerfectoidization_of_rootedGeneratingFamilyBaseChange`は、
R,Tのperfectoid性・R→S全射・Sの実導来p完備性・Tのp完全忠実平坦性と
f:S→ₐ[R]CのIsPerfectoidizationから、元のfの全射性を結論する。
Witt余積の候補・比較・G1の自然性と降下を内部で供給する。
核の全元の根、拡大のAIC、生成族の有限性、p正則性は要求しない。
2公開定理の対象3309ジョブ成功。B4専用監査を行う。

引用なしの根付き拡大の必要部分は、任意perfectoid Rと元族a:σ→Rについて
p完全忠実平坦perfectoid Tと各a_sの像の両立する根を供給する型で足りる。
後続の一般B4へはこの証明済みの弱い入力の降下を使う。
拡大の全元の根やAICを無用に構成目標へ追加しない。
拡大の存在そのものは未実装であり、B4完成ではない。

具体的q:R→Sとf:S→Cを入力する
`surjective_of_isPerfectoidization_of_sourceKernelRoots`も公開。
元の核Jの各元の像に根を供給するTだけで降下できる。
呼出側にR-代数構造を新しく要求せず、qとf∘qから内部で供給する。
この3公開定理により、B4-6の予定入力（元族の像の根）と一般降下の接続が揃った。
引用なしの拡大の存在を仮定して結果を完成扱いにしない。

最新検証：3公開定理の対象3309ジョブとB4専用全公開宣言監査成功。
標準3公理のみ。pure降下のプロジェクト内import閉包228件に
Inputs・CLMST・Paper・RootTowerなし。

引用なしの拡大構成に向けて著者版Prop 3.13（pp.33–35）と
Rem 7.15（p.62）を再確認した。Rem 7.15のcoverはProp 7.10に依存し、
pd表示だけから忠実性を既証明とは扱えない。正本§5もこの点を明示した。
次のBS専用計算候補は`FreeDeltaFrobeniusFlat.lean`：既存
FreeDeltaRing σ=MvPolynomial (σ×ℕ) ℤと
freeDeltaFrobenius p σ（X(s,n)↦X(s,n)^p+p X(s,n+1)）について、
有限段のモニック関係式による加群表示とFrobenius射の平坦性を調べる。
その計算の成立、完備化後の保存、δ除算包のp,d完全平坦性・忠実性が
証明されるまで、Prop 3.13の必要な制限版を供給済みとはしない。
共有のTor・完備性・完全平坦性の定義は再利用し、同等の定義を作らない。

この区切りの最終検証：対象ビルド・pure B4専用全公開宣言監査成功、
全体4519ジョブ成功。公開されたpure定理は標準3公理のみ。
生成族を使う降下のimport閉包228件にInputs・CLMST・Paper・RootTowerなし。

## B4-6：多項式Frobeniusのmod p基底への準備（2026-10-15）

予定BS専用モジュール`PolynomialExponentDivMod.lean`、
`PolynomialExpandDecomposition.lean`、`PolynomialExpandFree.lean`を追加する。
有限台指数の各座標をn>0で割り、n未満の余り指数と商指数へ分解する
具体的同値と逆式を前者で証明した。任意個の変数を含む。
この計算をMathlibのFinsupp同値とcurryへ接続し、
expand射の自由性から多項式Frobeniusのmod p平坦性を供給する。
3公開宣言の対象3134ジョブ成功。BS専用監査を行う。
混標数の自由δ環のFrobenius、完備化後の平坦性、必要な除算包の
完全忠実平坦性の証明とは区別する。

## B4-6：expandの単項式分解（2026-10-15）

`PolynomialExpandDecomposition`で、指数の商・余りの同値を
Mathlibの係数Finsupp・線形同値・curryへ接続した。
MvPolynomial σ R≃ₗ[R](n未満の指数→₀MvPolynomial σ R)を構成し、
逆射の単項式上の具体的な式を証明。任意個の変数・任意可換係数環を含む。
2公開宣言の対象3150ジョブ成功。B4専用監査を行う。
まだexpand作用に関する自由性とは区別し、次工程でその線形結合の
全単射性と基底を証明する。

## B4-6：多項式expand射の自由性と忠実平坦性（2026-10-15）

`PolynomialExpandFree`で、expand射によるスカラー作用を具体化した。
台環はMathlib標準ULift多項式環であり、指数nを持つ型名は通常の
係数環の自己作用とexpand作用を区別するためにだけ用いる。
多項式・平坦性・テンソル積の定義はMathlibを再利用する。
商・余り分解と単項式線形結合が互いに逆になることを証明し、
expand作用に関する具体的基底とModule.Freeを構成した。
Module.Flatと、非零係数環のModule.FaithfullyFlatは既存APIから供給する。
任意可換係数環・任意個の変数・n>0を含む。
11公開宣言の対象3162ジョブ成功。B4専用監査を行う。
次に素数体上のFrobeniusとの一致と自由δ環のmod p射への接続を証明する。
混標数φ・その完備化・δ除算包の完全忠実平坦性はまだ未証明。

## B4-6：素数体係数の多項式Frobenius（2026-10-15）

予定BS専用`PrimePolynomialFrobeniusFlat.lean`と`FreeDeltaModP.lean`を追加。
前者で素数体上のFrobeniusがexpand pそのものであることを
MathlibのFermat計算と多項式環の外延性から証明した。
既構成の単項式基底を使い、そのFrobenius作用でModule.Freeと
Module.FaithfullyFlatを証明。任意個の変数を含む。
係数環と変数集合の宇宙を分離し、既存のexpand APIを弱めず一般化した。
3公開定理の対象3163ジョブ成功。B4専用監査を行う。
次に自由整数δ環のmod pとの具体的商同型とFrobeniusの図式を供給する。
混標数のFrobenius・完備化・除算包の平坦性を証明済みとはしない。

## B4-6：自由整数δ環のmod p表示（2026-10-15）

`FreeDeltaModP`で、係数を素数体へ写す実際の標準射を定義し、
全射性と核=(p)を証明した。核の逆包含は、各整数係数をpで割った
具体的な多項式を作り、係数がpの倍数であることを使って証明。
標準商同型と代表元上の式、自由δ環のFrobeniusのmod p図式を公開した。
6公開宣言の対象2059ジョブ成功。B4専用監査を行う。
予定BS専用`FreeDeltaFrobeniusModPFlat.lean`で、素数体のexpand作用との
半線形同値を通して実際の剰余Frobeniusの自由性・忠実平坦性へ移す。
混標数・実完備化後の完全平坦性、必要な根付き拡大の存在はまだ未実装。

## B4-6：実際の自由δ環のmod p Frobeniusの自由性（2026-10-15）

`FreeDeltaFrobeniusModPFlat`で、標準商同型が実際のmodPMap p freeDeltaFrobeniusを
素数体のexpand射へ移す図式を証明。
標準ULiftの作用と素数体のexpand作用を結ぶ具体的半線形同値を構成し、
MathlibのModule.Freeの半線形同値による移送を使って自由性を証明した。
剰余環の非零性と既存APIから忠実平坦性も証明した。
公開結果は実際の剰余環の実際の剰余Frobenius作用に関するものであり、
素数体モデルだけを仮定した条件付き平坦性ではない。
9公開宣言の対象3209ジョブ成功。pure B4専用監査を行う。
一般pねじれperfectoid環のp正則性を要求する結果とは区別する。

## 共通基盤への要求 G3：正則主元と剰余平坦性からの完全平坦性

対象：R:Type u可換環、a:R、M:Type u加法群、Module R M。
正確な仮定：Function.Injective (fun r:R↦a*r)、
Function.Injective (fun m:M↦a•m)、
Module.Flat (R/span{a}) ((R/span{a})⊗[R]M)。
必要な結論：既存IsCompletelyFlat (Ideal.span {a}) M。
すなわちaで消える任意のR加群Nについて、既存derivedTensor R M Nが
次数0に集中することを証明する主元のTor基底変更判定。
剰余テンソルがModule.FaithfullyFlatなら、上の結論と既存定義を組み合わせて
IsCompletelyFaithfullyFlat (Ideal.span {a}) Mへ接続できる。
完備性・Noether性・有限生成性を要求しない形を使う。

利用：B4-6の自由δ環のFrobeniusの混標数完全平坦性への接続。
この工程の係数環は自由整数δ環でp正則、Frobeniusによるpの作用も通常のp作用。
元の一般perfectoid環Rがp正則という仮定は追加しない。
不足：既存CompletelyFlatPowerTorsionには完全平坦性から剰余平坦性への
方向があるが、この逆方向の主元正則性を使う公開入口は調査で確認できなかった。
共通Torと完全平坦性の定義・一般補題をBS内に重複して実装しない。
待つ工程：この混標数Tor判定の適用のみ。
独立作業：有限段モニック関係式、δ除算包の剰余表示・正則性、
根の具体的な構成と、その後の完備化に必要な比較条件の計算を進める。
要求の記録を外部への依頼メッセージや受領済み証明と同一視しない。

この区切りの最終検証：新規34公開宣言の対象ビルドとpure B4専用
全公開宣言監査成功。新規sorry・公理・引用依存なし、標準3公理のみ。
全体4536ジョブ成功。実際のmod p Frobeniusのモジュールの
プロジェクト内import閉包17件にInputs・CLMST・Paper・RootTowerなし。
BS専用6ステップとして検証済み変更のみコミットする。

## B4-6：δ除算の最初のモニック剰余関係式（2026-10-15）

予定BS専用`DeltaDivisionResidueRelation.lean`を追加。
δ環内の実際の関係式d*x=aにδを適用し、p,dを消す任意の通常環射qで
q(δd)*(q x)^p=q(δa)となることを証明した。
δdの像の単元uを指定したモニック冪方程式と、
既存DeltaAdjoinDivisionの初期変数に対する具体的な方程式を公開。
次数pのモニック多項式とその根であることを証明し、
dのdistinguished性から必要な単元を実際に供給する存在定理も証明した。
剰余環にδ構造を要求せず、一般pねじれ・零終域・任意添字の元族を含む。
5公開定理の対象2059ジョブ成功。B4専用監査を行う。

この最初の関係式だけではδ閉包全体の有限段表示や平坦性は結論しない。
後続のδ反復関係式、有限段のモニック表示、完全化・実完備化による
比較と平坦性・忠実性は引き続き必要。G3の受領なしでもこの剰余計算は進められた。
G3の公開入口は現時点の共通コード・計画で確認できず、共有ファイルは編集していない。
根付き完全忠実平坦拡大の存在、一般B4・B-S引用解消は未完了。
