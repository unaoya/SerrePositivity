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

## B4-6：通常剰余射の下でのδ反復算術（2026-10-15）

予定BS専用`DeltaResidueArithmetic.lean`、
`DeltaDivisionSecondResidueRelation.lean`を追加する。
前者で、pを消す射の下でδ(p)=1、δ(x^p)=0になることを
既存の合同式・δ冪の可除性から証明した。
片側が零に写る和のδ補正項は、MathlibのWitt座標自然性と
Teichmüller元の係数から直接消えることを証明。
pを消す射の下でのδ積公式も公開した。
剰余環にδ構造を要求せず、零環・一般pねじれも含む。
5公開定理の対象ビルドとB4専用監査を行う。
この計算を二段目のδ除算関係式の単元係数のモニック表示へ接続する。
δ(p*t)の剰余は一般に零ではないので、これを黙って消さない。

## B4-6：二段目のδ除算のモニック剰余関係式（2026-10-15）

`DeltaDivisionSecondResidueRelation`で、p,dを消す射の下での
δ²(d*x)=δ²(d)*x^(p²)+δ(d)^p*δ(x)^pを証明した。
源でδを計算してから写すため、δ(p*t)から来るt^pの項を正しく残す。
distinguished dの単元δdを使い、δ(x)のp乗をモニック方程式として解いた。
既存の実際のDeltaAdjoinDivisionへ適用し、初期変数のδの冪方程式・
モニック多項式・その根を証明し、必要な単元の存在も供給した。
最初の方程式を使ってx^(p²)を除き、二段目の係数を基底δデータと
単元だけで表す一般版と実際の添加環の版も公開した。
一般pねじれ・零終域・任意元族を含み、p正則性は要求しない。
7公開定理の対象ビルドとpure B4専用監査を行う。

この計算は最初の二段を扱う。全反復段の関係式がこれらだけで
生成されること、有限段全体の表示、平坦性・忠実性を結論していない。
次の独立工程は、一般段の三角形の関係式とモニックなp冪根関係式の
有限段加群表示をつなぐこと。必要な根付き拡大の存在はまだ未実装。
G3の未受領をB4全体の停止条件にせず、独立計算を続ける。

この区切りの最終検証：新規17公開定理の対象ビルドと
pure B4専用全公開宣言監査成功。公理は標準3公理のみ。
全体4544ジョブ成功。二段目の剰余計算のimport閉包15件に
Inputs・CLMST・Paper・RootTowerなし。
次のBS専用予定`MonicPowerFamilyCover.lean`では、Mathlibのexpand作用の
自由加群を係数評価で基底変更し、X_s^n=c_sというモニック関係式の
具体的な根添加環と、その通常の平坦性を構成する候補を調べる。
この通常根添加環をperfectoid拡大やその実完備化と同一視しない。
一般段のδ関係式との比較を証明するまで、必要な除算包の平坦性に
この有限段の結果を適用済みとは扱わない。

## B4-6：通常のモニック冪根添加環の構成（2026-10-15）

`MonicPowerFamilyCover`で、任意可換環R・任意元族c:σ→Rとn>0について、
X_s^n=c_sの指定根を持つ通常のR-代数を具体的に構成した。
Mathlibのテンソル積と既証明のexpand作用の加群を、係数評価で基底変更する。
テンソル積の右因子のModule構造を明示し、通常の自己作用との混同を避けた。
指定した根のn乗が元の像になることを実際のテンソル関係式で証明した。
Module.Free、Module.Flatと、非零RのModule.FaithfullyFlatを既存基底変更APIから供給。
零Rの枝も加えたModule.FaithfullyFlat版を証明し、任意個の元を同時に扱う。
有限性・Noether性を仮定しない。10公開宣言の対象3163ジョブ成功。
B4専用監査を行う。

次のBS専用予定`MonicPowerFamilyUniversal.lean`で、指定根を保つ写像の
普遍性を証明する。既存coefficientTensorLiftの係数環・両因子・終域の
宇宙を分離して再利用し、同等の一般テンソル射を作り直さない。
この通常根添加環をperfectoid拡大やその実完備化と同一視しない。
δ除算包との有限段表示の比較・全段の三角形の関係式・実完備化による
完全忠実平坦性の保存は未実装。一般B4完成とは数えない。

## B4-6：通常根添加環の指定根を保つ普遍性（2026-10-15）

`MonicPowerFamilyUniversal`で、通常根添加環の右因子の標準射、
係数と指定根上の式、係数と根で射が決まる外延性を証明した。
任意の通常環U、f:R→Uとb:σ→U、b_s^n=f(c_s)を入力し、
具体的な環射と係数・根の図式、一意存在を証明した。
完備性・perfectoid性・p正則性・有限性を仮定しない。
既存coefficientTensorLiftの2宣言の宇宙を分離して再利用し、
係数環・両因子・終域が別の宇宙にある場合も使えるようにした。
同等の一般テンソル射は追加しない。変更に依存するWitt余積と
既存の全射性降下の対象3314ジョブも再ビルド成功。
9公開宣言の対象3165ジョブ成功。B4専用監査を行う。

次のBS専用予定`MonicPowerFamilyCompleteFlat.lean`では、この具体的な通常環を
既存IsCompletelyFaithfullyFlatへ接続する。一般Tor判定を重複せず、
証明済みtorModule_subsingleton_of_flatと既存忠実平坦基底変更を使う。
δ除算包の有限段表示との同型・全段表示・実完備化の比較は未実装。
通常の根添加環をperfectoid拡大と同一視しない。一般B4完成ではない。

## B4-6：通常冪根添加環を完全忠実平坦性へ接続（2026-10-15）

`MonicPowerFamilyCompleteFlat`で、具体的な通常根添加環の通常平坦性を
既存torModule_subsingleton_of_flatとderivedTensorの次数0集中判定へ接続し、
任意のイデアルIについてIsCompletelyFlat Iを証明した。
剰余の忠実平坦性は既存の任意基底変更の保存APIを使い、
IsCompletelyFaithfullyFlat Iも証明した。零係数環を含む。
一般Tor判定・完全平坦性・完全忠実平坦性の定義を作り直していない。
共通IsCompletelyFlatの現在の宇宙に合わせ、この入口のRと添字σはType u。
2公開定理の対象3328ジョブ成功。B4専用監査を行う。

結果は未完備の通常根添加環についてであり、そのperfectoid性、
実完備化後の完全忠実平坦性、δ除算包の実際の有限段との比較は未結論。
次のBS専用予定`MonicPowerFamilyPresentation.lean`で、
MvPolynomial σ R/(X_s^n-c_s)という実際の商表示と標準写像の両立を証明する。
その後、δ関係式の有限段のモニック表示との比較に適用する。
全反復段の表示、必要な根付きperfectoid拡大の構成、一般B4完成は未実装。
G3の受領をこの独立作業の開始条件にしない。

この区切りの最終検証：新規21公開宣言の対象ビルドと
pure B4専用全公開宣言監査成功。公理は標準3公理のみ。
coefficientTensorLiftの宇宙一般化に依存するWitt余積・全射性降下の
対象3314ジョブも再検証成功。全体4573ジョブ成功。
通常根添加環の普遍性・完全忠実平坦性のimport閉包13件に
Inputs・CLMST・Paper・RootTowerなし。
検証済みBS成果だけ3ステップに分けてコミットする。

## B4-6：通常冪根添加環の実際の商表示（2026-10-15）

`MonicPowerFamilyPresentation.lean`で、任意R・任意族c:σ→R・任意nについて
span{X_s^n-C(c_s)}による多項式商と通常根添加環の具体的なR代数同型を証明した。
評価射がイデアルを消すこと、指定根の普遍射による逆写像、両合成の恒等性、
標準係数と変数の図式を含む。n>0・有限性・Noether性をこの同型には要求しない。
12公開宣言の対象3166ジョブとpure B4全公開宣言監査成功。
追加公理・sorry・引用なし。公理は標準3公理のみ。
前区切りの完全忠実平坦性のコミットはb703486。

次のBS専用予定`DeltaDivisionResiduePowerCover.lean`で、δ除算包の(p,d)剰余に
最初の通常冪根添加環からの実際の射を構成する。既証明のモニック方程式を
標準変数上の図式へ接続し、全段の生成性・同型・平坦性とは区別する。
δ除算包全反復段の三角形の表示、完備化とperfectionの完全忠実平坦性の保存、
必要な根付きperfectoid拡大の構成はなお未実装。一般B4の完成とは数えない。

## B4-6：δ除算包の実際の剰余への初期根添加射（2026-10-15）

`DeltaDivisionResiduePowerCover.lean`で、任意係数イデアルIとその像を消す
q:DeltaAdjoinDivision D d a→Bを入力し、A/Iからの係数射と
c_s=mk_I(δ(d)^{-1}δ(a_s))を具体的に定めた。
p,dの像が0なら、初期変数の剰余はc_sのp乗根となる。
これから通常冪根添加環の普遍射を構成し、係数と根の図式を証明した。
さらにdistinguished dの仮定のみから単元を取り出し、
I=(p,d)、J=(p,j(d))、B=DeltaAdjoinDivision D d a/Jという
実際の環・標準商射に対する存在定理を証明した。任意添字・零環を含む。
7公開宣言の対象3192ジョブ、pure B4全公開宣言監査成功。
全体4582ジョブ成功。新sorry・公理・外部引用なし、標準3公理のみ。

この射は全射・単射とは未結論。商先ではa_sの像も0になり得るため、
通常根添加環の忠実平坦性をこの射やδ除算包へ移すことはできない。
著者版Prop3.13 pp33–35は元のB上の平坦性を主張していないことも再確認した。
原典は基底A上の相対正則性、実際の導来pushoutとCor2.44・2.39を使う。
初期段のモニック方程式だけで原典の平坦性を代替しない。
次は全δ反復変数の三角形の関係式と生成イデアルを確認し、
適切な係数商上の有限段表示を構成する必要がある。
完備化/perfectionの比較、必要なperfectoid完全忠実平坦拡大と一般B4は未完。

## B4-6：δ除算包の全反復関係式による表示（2026-10-15）

`DeltaDivisionIteratedRelations.lean`で、生成イデアルのδ閉包を
元の指定生成元だけの全反復δ像で生成する通常イデアルと同定した。
既存deltaClosure_eq_span_iteratesはイデアル全体の像を入力していたため、
既存isStable_spanを再利用して指定生成元へ絞った。
実際のδ除算関係式δ^n(C(d)X_(s,0)-C(a_s))を定義し、
これらが定義イデアル全体を生成し、標準商で零になることを証明した。
初期変数の反復δ像とX_(s,n)の商像の一致も証明した。
全関係式を消す通常の環射は、終域のδ構造なしに一意に商へ降りる。

さらに深さN以下の通常関係式イデアルを定義し、単調性と
その上限が実際のδ閉包であることを証明した。添字族σは任意であり、
有限深さと有限個の生成元を混同しない。
13公開宣言の対象2060ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。

なお関係式の全段表示から、三角形のモニック方程式の表示・単射・平坦性は
まだ推論できない。有限深さのイデアルは一般にはδ安定でないため、
既存のδ商構造をそのまま与えない。
次のBS専用予定`DeltaDivisionFiniteResidueRelation.lean`では、
通常商への環射が低次の関係式を消すという仮定から、最初の冪方程式を
導く。実際のδ除算包内での等式に依存する既存定理とは区別し、
有限段の通常イデアルで使える入口を作る。
全段の三角形の係数制御、適切な係数商上の有限段同型、
実完備化/perfectionの完全忠実平坦性と一般B4はなお未実装。

## B4-6：有限深さの通常剰余での初期モニック方程式（2026-10-15）

`DeltaDivisionFiniteResidueRelation.lean`で、源でd*x=aを仮定せず、
通常射qがp,d,d*x-a,δ(d*x-a)を消すことから、
(qx)^p=(qδd)^{-1}qδaを証明した。商のδ安定性・δ構造は不要。
q(a)=0の導出、δ符号と差の剰余公式、最初のδ関係式の具体的な像を含む。
さらにp,dを消す射について、二つの低次関係式の消滅と
q(a)=0およびモニック冪方程式が同値であることを証明した。
通常イデアルの両方向の比較に使える。

相対自由δ環の深さ0,1の関係式への適用と、
J=span{p,C(d)} ⊔ deltaDivisionFiniteRelationIdeal D d a 1という
実際の通常商での冪方程式も証明した。
δ除算包全体の安定商に進む前の段階で成立する。
8公開宣言の対象2072ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・外部引用なし。

次のBS専用予定`DeltaDivisionFirstResiduePresentation.lean`で、
Jをspan{p,C(d),C(a_s),X_(s,0)^p-C(δ(d)^{-1}δ(a_s))}という
通常イデアルと同定する。適切な係数商はa_sの像も消す必要がある。
その後、初期変数と残りの変数を分けた商同型を構成する。
全段の三角形の表示、実完備化/perfectionの完全忠実平坦性、
根付きperfectoid拡大と一般B4の引用解消はなお未実装。

## B4-6：初期剰余イデアルのモニック表示への同定（2026-10-15）

`DeltaDivisionFirstResiduePresentation.lean`で、p,C(d)と深さ0,1のδ関係式の
通常イデアルを、p,C(d),C(a_s)と
X_(s,0)^p-C(δ(d)^{-1}δ(a_s))で生成する通常イデアルに同定した。
δ(d)を表すAの単元を明示的に入力する。零環・任意添字を含み、
p正則性・d正則性・Noether性・有限性を仮定しない。
両イデアルを消す通常射の判定をそれぞれ証明し、前工程の関係式消滅の
同値を使って判定を比較し、実際の標準商射の核からイデアル等式を得た。
実際の商同型と標準商射上の図式も公開した。
7公開宣言の対象2073ジョブ、pure B4全公開宣言監査成功。
公理は標準3公理のみ。新sorry・公理・外部引用なし。

次のBS専用予定`RelativeFreeVariableSplit.lean`で、σ×ℕを初期変数σと
残りの変数σ×ℕへ分ける明示的な同値と多項式環の同型、係数・変数上の式を
構成する。その後`DeltaDivisionFirstResiduePowerPresentation.lean`で、
適切な係数環A/(p,d,a_s)上の初期根添加環と残りの自由変数という
表示へ接続する。既存MonicPowerFamilyPresentationを再利用する。
この初期段の同定を全δ段の表示や基底A上の平坦性と同一視しない。
全段のモニック三角形表示、実完備化/perfectionの完全忠実平坦性と
根付きperfectoid拡大・一般B4の引用解消はなお未実装。

## B4-6：相対自由変数の初期段と後続段の分離（2026-10-15）

`RelativeFreeVariableSplit.lean`で、σ×ℕ≃(σ×ℕ)⊕σを具体的に構成し、
初期変数を係数側へ、後続変数を外側へ送るA代数同型
RelativeFreeDeltaRing σ A ≃ MvPolynomial (σ×ℕ) (MvPolynomial σ A)を証明した。
既存MathlibのrenameEquiv・sumAlgEquivを再利用する。
係数・初期変数・後続変数上の式と逆向きの式、
初期多項式と後続多項式の標準包含との図式を証明した。
σとAの宇宙は独立。δ構造保存や平坦性はこの同型から主張しない。
14公開宣言の対象2056ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。

次は予定済みDeltaDivisionFirstResiduePowerPresentationで、
初期モニックイデアルを分離した環の係数イデアルに移し、
通常商をA/(p,d,a_s)上の初期根添加環に後続自由変数を添加した環へ接続する。
係数の商と変数の商の比較には既存Mathlibの多項式商APIを優先する。
全δ段の三角形表示、実完備化/perfectionの完全忠実平坦性、
根付きperfectoid拡大と一般B4完成は未実装。

## B4-6：初期商を係数とする後続多項式の表示（2026-10-15）

`DeltaDivisionFirstResiduePowerPresentation.lean`で、初期変数のみの多項式環に
p,C(d),C(a_s)とX_s^p-C(δ(d)^{-1}δ(a_s))のイデアルを具体的に定義した。
変数分離同型が実際の初期δ剰余イデアルを、この係数イデアルの延長へ送ることを
証明した。Mathlib quotientEquivQuotientMvPolynomialを再利用し、
実際の初期δ剰余と、初期多項式商上の後続変数の多項式環の同型を構成した。
標準商射、元の係数、初期変数、後続変数上の図式も証明済み。
同等の一般多項式商比較を作り直していない。
8公開宣言の対象2075ジョブ、pure B4全公開宣言監査成功。
全体4590ジョブ成功。標準3公理のみ。新sorry・公理・外部引用なし。

初期多項式商をMonicPowerFamilyCoverと同定する比較はまだ必要である。
次のBS専用予定`DeltaDivisionFirstCoefficientPowerEquiv.lean`で、
係数イデアルI=span{p,d}⊔span{a_s}とc_s=mk_I(δ(d)^{-1}δ(a_s))を定め、
初期多項式商とMonicPowerFamilyCover p σ (A/I) cの標準同型を証明する。
既存の指定根の普遍性と標準商射の降下を使い、係数・根の図式を含める。
その後、後続多項式表示へ同型を適用して、既証明の通常自由性・忠実平坦性を
適切な係数商について接続する。元のA上の平坦性とは同一視しない。
全δ段の三角形表示、実完備化/perfectionの完全忠実平坦性と
根付きperfectoid拡大、一般B4の引用解消は未実装。

## B4-6：初期係数商と通常根添加環の具体的な同型（2026-10-15）

`DeltaDivisionFirstCoefficientPowerEquiv.lean`で、
I=span{p,d}⊔span{a_s}、c_s=mk_I(δ(d)^{-1}δ(a_s))と
MonicPowerFamilyCover p σ (A/I) cを具体的に定義した。
初期係数多項式商から指定根への評価射を構成し、実際のイデアルを消すことを証明。
逆向きは基底商の係数射と指定根の普遍性を使って構成し、
係数・根の外延性と通常商の外延性から両合成の恒等性を証明した。
初期係数商と通常根添加環の標準同型、係数・根の図式を公開した。
この係数商比較は任意単元uで成立する。実際のδ剰余への比較にはu=δ(d)を要求する。

既存の後続変数表示と組み合わせ、実際の初期δ剰余を
A/(p,d,a_s)上の通常根添加環に後続変数を自由添加した環と同定した。
初期変数の剰余は指定根の係数像、後続変数は外側の自由変数となる。
零環・任意添字を含み、p正則性・Noether性・有限性・完備性を仮定しない。
26公開宣言の対象3204ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・外部引用なし。

次のBS専用予定`DeltaDivisionFirstResidueFlat.lean`で、この実際の初期商に
適切な基底商A/Iの代数構造を与え、通常根添加環と多項式環の既存自由性・
忠実平坦性を同型に沿って移す。係数射の標準商射との両立も明示する。
元のA上の忠実平坦性は結論しない。
全δ段の三角形表示と有限段比較、実完備化/perfectionの完全忠実平坦性、
根付きperfectoid拡大と一般B4の引用解消は未実装。

## B4-6：実際の初期剰余の自由性と完全忠実平坦性（2026-10-15）

`DeltaDivisionFirstResidueFlat.lean`で、A/(p,d,a_s)から実際の初期δ剰余への
係数射を定義し、元の係数の標準商像との一致を証明した。
同型に沿った代数構造を与え、通常根添加環上の後続多項式表示を
この標準係数射についての代数同型として公開した。
既存の基底・通常根添加環の自由性・直和の忠実平坦性を用い、
実際の初期δ剰余の自由性、通常平坦性、忠実平坦性を証明した。
零環も含む。係数と添字の宇宙を通常版では分離している。

既存Tor消滅と剰余忠実平坦基底変更に接続し、
適切な係数商の任意イデアルに関してIsCompletelyFlatと
IsCompletelyFaithfullyFlatも証明した。この二つの入口は共通APIに合わせ
係数と添字をType uに置く。一般Tor補題・完全平坦性の定義は追加しない。
12公開宣言の対象3369ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。

結果は通常未完備の深さ0,1の関係式商についてである。
A/(p,d,a_s)上の平坦性を元のA上へ移すことはできない。
次のBS専用予定`DeltaDivisionSecondFiniteResidueRelation.lean`で、
深さ0,1,2の関係式を消す通常射から、次の変数のモニック冪方程式を導く。
既存の実際のδ除算包での第2剰余計算を、そのまま有限深さイデアルの
δ安定性に読み替えない。加法補正項のδ像・δ差の反復の比較が必要である。
全段の三角形の表示、実完備化/perfectionの完全忠実平坦性、
必要な根付きperfectoid拡大と一般B4引用解消は未実装。

第2有限段の補助予定（BS担当）：`DeltaAdditionCarryProduct.lean`で、
Witt加法の第1補正項がx*yで割り切れることを、整数係数の二変数多項式の
標準商と既存の変数素元APIから証明する。既存delta_mem_powを使い、
p,x,yを消す射の下で補正項のδ像も消えることへ接続する。
一般共通Witt補題を重複せず、BSのδ有限段計算の補助モジュールとして置く。

## B4-6：第2有限段の加法補正項のδ像（2026-10-15）

`DeltaAdditionCarryProduct.lean`で、Witt第1加法補正項が入力x*yで割り切れることを
整数係数二変数の標準商と既存の変数素元APIで証明した。
両入力がIに属せば補正項はI²に属する。既存delta_mem_powにより、
pと両入力を消す通常射の下では補正項のδ像も消える。
これから第2δの加法公式と、差・そのδ像・δ²像を消す通常射の下での
δ²値の一致を証明した。右入力の零像も明示した。
商のδ構造・p正則性・完備性を要求しない。
5公開定理の対象2067ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
第2有限段の次変数のモニック方程式に適用する。

## B4-6：第2有限段のモニック冪方程式（2026-10-15）

`DeltaDivisionSecondFiniteResidueRelation.lean`で、通常射qがp,dと
r=d*x-a,δr,δ²rを消すことから、qδxのp乗を基底のδ²a,δ²dとqxで表した。
既証明の第1方程式を使い、係数を基底δデータと単元だけへ直した版も公開。
源でd*x=aが成立することや、有限深さの通常商のδ安定性を要求しない。
前工程のδ²差の比較を使い、実際のδ除算包内の等式を仮定する従来版と区別する。
相対自由δ環で深さ0,1,2の指定関係式を消す射へ適用し、
X_(s,1)のp乗の係数を明示した。零環・任意添字を含む。
3公開定理の対象2078ジョブ、pure B4全公開宣言監査成功。
全体4601ジョブ成功。新sorry・公理・引用なし。標準3公理のみ。
前工程の補正項制御はb29d628に個別コミット済み。

次のBS専用予定`DeltaDivisionSecondFinitePresentation.lean`で、
実際のJ₂=span{p,C(d)}⊔deltaDivisionFiniteRelationIdeal D d a 2に適用し、
標準商での第2冪方程式と、低次関係式の消滅からの逆向き比較を証明する。
三つの関係式と係数・二つのモニック方程式のイデアルを同定し、
適切な係数商上の二段の通常根添加表示へ接続する。
全反復段への一般化・有限段の基底比較、実完備化/perfectionの
完全忠実平坦性、根付きperfectoid拡大と一般B4の引用解消はなお未実装。

## B4-6：第2有限段の逆向き判定と標準商への適用（2026-10-15）

`DeltaDivisionSecondFinitePresentation.lean`で、最初の二つの関係式が消える場合に
δ²関係式の消滅と次のモニック冪方程式が同値であることを証明した。
三つの関係式の消滅を、係数aの消滅と二つのモニック方程式に同定した。
通常射の下の第2δ加法を使い、有限段の商にδ構造を仮定しない。

J₂=span{p,C(d)}⊔deltaDivisionFiniteRelationIdeal D d a 2という
実際の通常イデアルを定義し、標準商でX_(s,1)のp乗を具体的な基底係数で表した。
さらに任意Nの有限深さ関係式イデアルについて、次の段の関係式を加える等式を
証明した。J₂を初期剰余イデアルとδ²関係式の和として表示する版も公開。
6公開宣言の対象2079ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。

次のBS専用予定`DeltaDivisionSecondMonicPresentation.lean`で、
基底δデータの第2係数を定義し、J₂を初期モニックイデアルと
X_(s,1)^p-C(c₁(s))の通常イデアルの和へ同定する。
各通常射の核への包含を、今回の両方向の消滅判定で比較する。
その後、二段の通常根添加環・後続自由変数の表示と自由性に接続する。
全段の三角形の表示と実完備化/perfectionの完全忠実平坦性、
必要な根付きperfectoid拡大と一般B4の引用解消は未実装。

## B4-6：第2通常イデアルの二つのモニック方程式への同定（2026-10-15）

`DeltaDivisionSecondMonicPresentation.lean`で、次の変数の係数c₁(s)を
基底δデータと単元だけで定義し、初期モニックイデアルに
X_(s,1)^p-C(c₁(s))を加えた通常イデアルを定義した。
初期関係式を消す通常射について、δ²関係式の消滅と次の冪方程式を
同定した。これで実際のJ₂と二段モニックイデアルの核包含条件を比較し、
標準商射の核からイデアル等式を証明した。
実際の標準商同型と商射上の図式も公開した。
有限段の商のδ安定性・p正則性・Noether性・有限添字性を要求しない。
7公開宣言の対象2081ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。

次のBS専用予定`RelativeFreeFiniteVariableSplit.lean`で、任意Nの
σ×ℕ≃(σ×ℕ)⊕(σ×Fin N)を具体的に構成し、有限初期段と後続段の
多項式環分離および標準変数・係数上の式を証明する。
第2段だけの添字分離を作らず、後の全有限段の表示に再利用する。
その後予定`DeltaDivisionSecondPowerPresentation.lean`で、
A/(p,d,a_s)上のσ×Fin 2の通常p乗根添加環と後続自由変数の表示へ接続する。
全δ段の三角形の表示・実完備化/perfectionの完全忠実平坦性、
必要な根付きperfectoid拡大と一般B4の引用解消は未実装。

## B4-6：任意有限初期段の変数分離（2026-10-15）

`RelativeFreeFiniteVariableSplit.lean`で、任意Nの添字同値
σ×ℕ≃(σ×ℕ)⊕(σ×Fin N)を具体的に構成した。
初期N段を係数多項式へ、N以降を外側多項式へ送るA代数同型を
既存MathlibのrenameEquiv・sumAlgEquivで構成し、
係数・両部分の変数・逆同型上の式と任意初期/後続多項式の標準包含図式を証明した。
N=0、任意添字、係数と添字の独立の宇宙を含む。
δ構造保存や平坦性は、この台多項式環の同型から主張しない。
14公開宣言の対象2056ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
第2モニックイデアルの係数イデアルへの移送に適用する。

## B4-6：第2商の有限初期係数商上の後続多項式表示（2026-10-15）

`DeltaDivisionSecondPowerPresentation.lean`で、σ×Fin 2の多項式環に
係数関係式と二つのモニック冪関係式のイデアルを定義した。
任意有限変数分離のN=2版で実際の第2剰余イデアルを、
この有限初期係数イデアルの延長へ移すことを証明した。
既存Mathlibの商同型を再利用し、第2通常δ剰余と
有限初期多項式商上の後続変数の多項式環の具体的な同型を構成した。
標準商射、元の係数、初期2変数、後続変数の図式を証明した。
10公開宣言の対象2083ジョブ、pure B4全公開宣言監査成功。
全体4608ジョブ成功。標準3公理のみ。新sorry・公理・外部引用なし。
有限変数分離はcf2407cで先に個別コミット済み。

有限初期係数多項式商と同時根添加環の比較はなお必要である。
次のBS専用予定`DeltaDivisionSecondCoefficientPowerEquiv.lean`で、
I=span{p,d}⊔span{a_s}、σ×Fin 2の係数族(c₀,c₁)を明示し、
有限初期係数商とMonicPowerFamilyCover p (σ×Fin 2) (A/I) cの同型を証明する。
既存の指定根の普遍性と商射の降下を再利用し、係数・両根の図式を含める。
その後、第2通常商の適切な係数商上の自由性・完全忠実平坦性に接続する。
全δ段の三角形表示と実完備化/perfectionの完全忠実平坦性、
根付きperfectoid拡大と一般B4の引用解消は未実装。

第2係数商の比較方法：BS専用予定`MonicPowerFamilyBaseQuotient.lean`で、
任意係数イデアルI・任意根係数族cについて、係数イデアルの延長と
モニック関係式による商を、R/I上の通常根添加環へ同定する。
Mathlibの係数商同型・二重商同型と既存MonicPowerFamilyPresentationを合成し、
一般の商比較や普遍射を新たに重複構築しない。全有限段で再利用する。

## B4-6：通常根添加の係数商比較を既存商同型から構成（2026-10-15）

`MonicPowerFamilyBaseQuotient.lean`で、任意係数イデアルI・任意族c・任意nについて
(Iの多項式環への延長)⊔(X_s^n-C(c_s))による商を、R/I上の通常根添加環へ同定した。
既存Mathlibの係数商・二重商・商同型とMonicPowerFamilyPresentationを合成する。
係数商同型と標準商射の合成、関係式イデアルの移送、標準商射・係数・根上の
図式も証明した。同等の一般商比較・普遍射を重複構築していない。
6公開宣言の対象3167ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
第2有限係数商へ適用中。全段・完備化後と一般B4は未完。

## B4-6：第2係数商と同時根添加環の同型（2026-10-15）

`DeltaDivisionSecondCoefficientPowerEquiv.lean`で、初期二つの基底係数を
σ×Fin 2の一つの係数族へまとめ、有限係数イデアルを
I=span{p,d}⊔span{a_s}の延長と同時モニックイデアルの和へ同定した。
MonicPowerFamilyBaseQuotientの既存商同型合成を適用し、
第2有限係数商をA/I上の具体的な同時p乗根添加環へ同定した。
標準商射・元の係数・両指定根の図式を含む。
さらに実際の第2通常δ剰余を、同時根添加環上の後続自由変数の多項式環へ
同定し、初期2変数と後続変数の図式を公開した。
終域のδ構造・p正則性・Noether性・有限添字性・完備性を要求しない。
11公開宣言の対象3216ジョブ、pure B4全公開宣言監査成功。
全体4612ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。
今回2モジュールのプロジェクトimport閉包38件にInputs・CLMST・Paper・RootTowerなし。
標準商射上の計算補題1件だけ、三つの商同型のカーネル比較に必要な
局所maxHeartbeats 1000000を設定し、理由をコメントに記録した。
対象のカーネル検証を含むビルドは116秒で成功した。
係数商比較は8e5c25dで先に個別コミット済み。

次のBS専用予定`DeltaDivisionSecondResidueFlat.lean`で、標準係数射に沿う
A/I代数構造を実際の第2商へ与え、既存の根添加・多項式環の自由性と
忠実平坦性を同型に沿って移す。既存Tor APIで完全忠実平坦性にも接続する。
元のA上の忠実平坦性は結論しない。
全δ段の三角形表示と実完備化/perfectionの完全忠実平坦性、
必要な根付きperfectoid拡大と一般B4の引用解消は未実装。

第2商の平坦性の補助予定（BS担当）：`MonicPowerFamilyPolynomialFlat.lean`で
通常根添加環上の任意後続多項式環の自由性・忠実平坦性を、既存基底・直和APIで
証明する。各有限段で直和計算を作り直さず、この具体的な根添加環APIへまとめる。
一般Tor判定や完備化後の平坦性を新たに定義・仮定しない。

## B4-6：通常根添加環上の任意後続多項式環の自由性（2026-10-15）

`MonicPowerFamilyPolynomialFlat.lean`で、n>0の通常根添加環上に任意変数族τを
自由添加した多項式環の、元の係数環R上の自由性・平坦性・忠実平坦性を証明した。
既存の係数基底、直和の忠実平坦性と線形同型の保存を使う。
零環・任意根族・任意後続変数族を含み、三つの宇宙を分離する。
各有限段で同等の基底・直和計算を作り直さず、この根添加環APIを再利用する。
3公開定理の対象3164ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。第2通常δ剰余へ適用する。

## B4-6：実際の第2通常剰余の自由性と完全忠実平坦性（2026-10-15）

`DeltaDivisionSecondResidueFlat.lean`で、適切な係数商A/(p,d,a_s)から
実際の第2通常δ剰余への係数射を構成し、元の係数の標準商射との一致を証明した。
同時根添加後続多項式表示を、この標準係数射についての代数同型にした。
MonicPowerFamilyPolynomialFlatを適用し、実際の第2商の自由性・通常平坦性・
忠実平坦性を同型に沿って証明した。各有限段で基底・直和計算を作り直さない。
さらに既存Tor消滅と剰余の忠実平坦基底変更を使い、
任意係数イデアルについてIsCompletelyFlatとIsCompletelyFaithfullyFlatを証明した。
零環・任意添字を含む。通常版の宇宙は独立、完全平坦性版は共通APIに合わせType u。
12公開宣言の対象3382ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
後続多項式APIは65f9f53で先に個別コミット済み。

対象は未完備のJ₂商、係数環はA/(p,d,a_s)である。
元のA上や全δ除算包、実完備化後の完全忠実平坦性とは区別する。
次のBS専用予定`RelativeFreeFiniteDeltaStep.lean`で、任意Nに対し
MvPolynomial (σ×Fin(N+1)) AからWittTwo p (MvPolynomial (σ×Fin(N+2)) Aへの
有限δ計算の環射を構成する。第0座標は変数の標準包含、第1座標は次の変数を使う。
元の相対自由δ切断とのWitt自然性・係数/変数の図式を確認し、
有限初期多項式のδ像が次の有限初期段に表せることを証明する。
同じ有限段にδ構造を与えるのではなく、一段大きい環でδ計算を表す。
全段の関係式の最高変数・モニック三角形表示への一般化を進める。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、一般B4は未実装。

有限δ計算の次のBS専用予定：`DeltaDivisionFiniteRelationPolynomial.lean`で、
任意nのδ反復除算関係式をσ×Fin(n+1)の具体的な多項式として再帰構成し、
標準包含の像が実際の反復関係式に一致することと、その変数段数の上界を証明する。
全有限段の最高変数・モニック三角形表示を扱うための入口にする。

## B4-6：任意有限段のδ計算と相対自由環の自然性（2026-10-15）

`RelativeFreeFiniteDeltaStep.lean`で、任意Nの有限W₂計算射を構成した。
初期N+1段の変数を、第0座標の標準包含と第1座標の次変数へ送る。
係数は既存の基底δ切断を使う。第0座標の環射は有限段の標準包含、
第1座標の具体的なδ計算は一段大きい初期N+2段に値を取る。
元の相対自由W₂切断との可換図式を係数・変数で証明し、
任意有限初期多項式の実際のδ像がこの有限計算の標準包含に一致することを証明した。
標準包含の単射性も既存rename_injectiveから供給した。
有限段自体にδ構造を与えず、p正則性・有限添字性・完備性を要求しない。
11公開宣言の対象2057ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
全反復関係式の具体的な有限表示に適用する。

## B4-6：全反復除算関係式の具体的な有限多項式表示（2026-10-15）

`DeltaDivisionFiniteRelationPolynomial.lean`で、任意nの反復除算関係式を
MvPolynomial (σ×Fin(n+1)) Aの具体的な多項式として再帰構成した。
有限δ計算の自然性を反復し、その標準包含の像が実際の
δ^n(C(d)X_(s,0)-C(a_s))に一致することを証明した。
実際の反復関係式の変数段数がn以下であることと、有限初期段の表示の一意性を
既存vars_rename・rename_injectiveへ接続して証明した。
任意深さ・任意添字・零係数環を含む。有限段のδ安定性は仮定しない。
6公開宣言の対象2063ジョブ、pure B4全公開宣言監査成功。
全体4623ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。
有限δ計算はc249477で先に個別コミット済み。

次のBS専用予定`RelativeFreeFiniteDeltaStepIdentities.lean`で、
有限段の標準包含の合成図式を確認し、δの加法・積公式を
任意有限δ計算へ移す。標準包含の単射性と既存δ公式を使い、
Wittの一般加法・積補題を重複構築しない。
その後、最高段の新変数に対する線形性とmod pでの冪の挙動を扱い、
全有限段のモニック三角形表示を証明する必要がある。
段数上界だけから最高変数の係数・モニック性・平坦性は結論しない。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、一般B4は未実装。

有限δ公式の次のBS専用予定：`RelativeFreeFiniteDeltaResidue.lean`で、
次の有限段のpを消す通常射の下でのFrobenius・δ積・δ加法を証明する。
同じ有限段のδ構造を仮定せず、既証明の有限W₂計算公式を使う。
最高段の新変数の係数を調べるための入口とする。

## B4-6：任意有限δ計算の加法・積・Frobenius公式（2026-10-15）

`RelativeFreeFiniteDeltaStepIdentities.lean`で、有限包含と相対自由環への
標準包含の合成図式、有限W₂計算の第0座標の点ごとの式を証明した。
既存Witt係数公式を有限W₂射へ適用し、δの零・単位・加法・積公式を
次の段への標準包含を明示した形で証明した。
有限Frobeniusの環射と具体式も構成し、実際の相対自由Frobenius像との一致を証明。
同等の一般Witt係数補題は構築し直していない。
9公開宣言の対象2058ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
pを消す通常射の下での有限剰余計算に適用する。

## B4-6：任意有限δ計算のp剰余公式（2026-10-15）

`RelativeFreeFiniteDeltaResidue.lean`で、一段大きい有限環からの通常射qと
q(p)=0を明示し、有限Frobeniusの像が標準包含のp乗になること、
δ積の第三項が消えることを証明した。包含像の左右いずれかが零なら、
δ加法の補正項も消えることを証明した。
有限δ積公式を反復して正整数冪の公式を証明し、δ(f^p)の像の消滅を得た。
既存基底δ(p)公式へ係数射を適用し、有限δ(p)の像が1になることも証明した。
有限商にδ構造を要求せず、CharP B pも要求しないので零終域を含む。
7公開定理の対象2070ジョブ、pure B4全公開宣言監査成功。
全体4630ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。
有限計算の公式は823011aで先に個別コミット済み。

次のBS専用予定`PolynomialRankOneDelta.lean`（BS担当）で、
基底δ環上の多項式の各変数をrank 1とする補助δ構造を既存W₂切断から構成する。
これは実際のδ変数が次の段へ移る有限δ計算とは異なる補助構造である。
係数上のδと変数のδ=0、第0座標条件を明示する。
その後予定`RelativeFreeFiniteDeltaLinearization.lean`で、q(p)=0の下で
有限δ計算と、この補助δ計算の標準包含との差を比較する。
差の加法・積公式と係数上の消滅、各変数の値を確認し、
既存Mathlibの多項式derivation APIで最高新変数の線形性へ接続する。
係数作用はqと有限Frobeniusの環射の合成を使い、零終域を落とさない。
この線形化・全有限段のモニック三角形表示は未証明。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、一般B4は未実装。

## B4-6：rank 1変数の補助多項式δ構造（2026-10-15）

`PolynomialRankOneDelta.lean`（BS担当）で、基底δ構造を係数に延長し、
各多項式変数のδを零とする補助W₂切断とδ構造を構成した。
第0座標条件、係数上のδと係数射のδ自然性、変数のδ=0とFrobenius像=X^p、
変数のp乗のδ=0を証明した。既存W₂・δ冪可除性を再利用する。
相対自由δ変数が次座標へ移る構造とは別の、比較に用いる補助構造である。
8公開宣言の対象2059ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
有限δ計算の差の線形化に適用する。

## B4-6：任意有限δ計算のFrobenius線形化（2026-10-15）

`RelativeFreeFiniteDeltaLinearization.lean`で、rank 1変数の補助δ像を
次の有限段へ含め、実際の有限δ像との差を構成した。
両計算の加法補正項が同じことから差の加法性を証明し、q(p)=0の下で
Frobenius係数作用のLeibniz公式を証明した。係数上の差は零、
各変数上の差はq(X_(s,i+1))である。

係数作用をqと有限Frobeniusの環射の合成で明示し、差を既存Mathlibの
Derivationとして構成した。スカラー作用はAlgebra.smul_defで確認した。
検証上限の変更を要さず対象ビルド2秒で成功。
既存MvPolynomial.derivation_extで指定変数値のmkDerivationに一致させ、
単項式と任意多項式の差を、次変数の像の具体的な有限線形結合として証明した。
その係数は初期変数のみの標準包含像のp乗で表せる。
CharP B p・非零性・完備性を要求せず、零終域を含む。
新しいderivationや一般Witt公式の定義は追加しない。
16公開宣言の対象2075ジョブ、pure B4全公開宣言監査成功。
全体4637ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。
補助δ構造はdd8cb58で先に個別コミット済み。

次のBS専用予定`RelativeFreeFiniteTopVariableSplit.lean`で、
σ×Fin(N+2)を最高変数σと初期変数σ×Fin(N+1)へ分け、
有限次段を最高変数の多項式環へ同定する。
次の予定`RelativeFreeFiniteDeltaTopDegree.lean`で、この同型と係数のp商から
通常射qを具体的に構成し、今回の有限線形結合の式から
有限δ像の最高変数全体に関するtotalDegree≤1を証明する。
係数商のδ構造は仮定しない。この次数評価と最高変数の係数計算から、
全有限段のモニック三角形表示へ進む。次数評価・係数計算はまだ未証明。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、一般B4は未実装。

## B4-6：有限次段の最高変数分離（2026-10-15）

`RelativeFreeFiniteTopVariableSplit.lean`で、任意Nの有限次段の添字を
最高変数σと初期変数σ×Fin(N+1)へ分ける具体的な同値を構成した。
既存renameEquiv・sumAlgEquivを使い、次段を初期変数の係数多項式環上の
最高変数多項式環に同定した。係数・最高変数・初期変数の像と、
任意初期多項式の次段への包含が分離後の係数射になる図式を証明した。
任意添字と零係数環を含む。
8公開宣言の対象2058ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
係数のp商を伴う具体的な射と次数評価に適用する。

## B4-6：任意有限δ像の最高変数次数はp剰余で1以下（2026-10-15）

`RelativeFreeFiniteDeltaTopDegree.lean`で、初期有限多項式環をpで割る係数環と、
最高変数分離後に係数をpで割る具体的な通常環射qを構成した。
q(p)=0、初期多項式の像が係数になること、最高変数・初期変数の像を証明した。
初期像の任意冪の次数0、次変数の像の次数1以下を確認し、
既証明の有限線形結合の式からδ差の最高変数全体のtotalDegree≤1を証明した。
rank 1補助δ像は係数側にあるので、実際の有限δ像についても同じ次数評価を得た。
係数商が零環の枝も証明し、CharPや非零性、係数商のδ構造を要求しない。
係数商・変数の射の定義と図式は任意pで成立し、δ次数評価でのみFact p.Primeを使う。
11公開宣言の対象2077ジョブ、pure B4全公開宣言監査成功。
全体4642ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。
最高変数分離は4ffefa7で先に個別コミット済み。

次のBS専用予定`RelativeFreeFiniteDeltaTopCoefficient.lean`で、
q(δ_step f)の外側変数X_sの係数を取り出す。
目標は、その係数が初期係数p商における
pderiv_(s,last N)(f)の像のp乗に一致すること。
既存の多項式derivation・係数線形写像・変数上の外延性を使い、
一般Wittや一般derivationの定義・補題を重複構築しない。
この係数公式と全反復関係式の有限表示から、全段の最高係数と
モニック三角形の関係式を制御する。係数公式・全段モニック表示は未証明。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、一般B4は未実装。

## B4-6：任意有限δ像の最高係数の偏微分公式（2026-10-15）

`RelativeFreeFiniteDeltaTopCoefficient.lean`で、初期rank 1補助Frobeniusとp商の
具体的な環射を構成し、その値が標準商像のp乗であることを証明した。
有限Frobeniusの最高変数分離後の像は、この初期Frobeniusの係数像となる。
実際の有限δ像の最高変数X_sの係数を定義し、補助rank 1δ像の寄与が零であること、
係数の加法性・Frobenius係数Leibniz公式・係数上の零・各有限変数での値を証明した。

既存多項式の帰納法と偏微分の公式から、任意fに対して最高係数が
pderiv_(s,last N)(f)の初期Frobenius商像に一致することを証明した。
すなわち、初期係数p商における偏微分像のp乗となる。
CharPや非零性、係数商のδ構造・完備性を要求せず、零係数商を含む。
既存derivation・Wittの一般定義や補題を追加し直していない。
11公開宣言の対象2079ジョブ、pure B4全公開宣言監査成功。
全体4649ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。

次のBS専用予定`RelativeFreeFiniteDeltaTopDerivative.lean`で、
次段の最高変数に関する実際の偏微分も制御する。
目標は任意通常射q（次段から、q(p)=0）の下で
q(pderiv_(s,last(N+1))(δ_step f)) = q(φ_step(pderiv_(s,last N)(f)))
が成立すること。初期包含多項式の最高偏微分が零であることと、
既存の有限δ加法・積公式、Witt補正項の包含自然性・多項式帰納法を使う。
この公式から全反復関係式の最高偏微分を、φ^n(d)の係数像としてp剰余で制御し、
全有限段のモニック三角形表示へ進む。偏微分公式・全段最高係数の反復は未証明。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、一般B4は未実装。

最高偏微分の次のBS専用予定：`DeltaDivisionFiniteTopDerivative.lean`で、
全深さnの有限除算関係式の最高偏微分のp剰余像を、対応する生成元では
φ^n(d)の係数像、別の生成元では零と証明する。
次段の通常射qと有限Frobeniusの合成を前段の通常射として使い、
pの消滅を環射のNat.cast保存から確認して、今回の公式を反復する。

## B4-6：任意通常p剰余での有限δ像の最高偏微分公式（2026-10-15）

`RelativeFreeFiniteDeltaTopDerivative.lean`で、初期包含多項式の最高偏微分が零、
有限δ加法補正項が初期補正項の包含像であることを証明した。
実際の有限δ像の最高偏微分を通常射で写し、加法性とq(p)=0の下での
Frobenius係数Leibniz公式を確認した。係数上の零と各変数での値から、
任意q（次段から、q(p)=0）・任意fに対して
q(pderiv_(s,last(N+1))(δ_step f)) = q(φ_step(pderiv_(s,last N)(f)))を証明した。
有限Frobeniusの係数上の式も公開し、基底Frobeniusへ一致させた。
CharP・非零性・完備性・有限商のδ構造を要求しない。
9公開宣言の対象2075ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
全反復除算関係式へ反復適用する。

## B4-6：全反復除算関係式の最高偏微分のp剰余像（2026-10-15）

`DeltaDivisionFiniteTopDerivative.lean`で、任意深さn・任意生成元t・任意通常射q
（初期n+1段から、q(p)=0）について、最高偏微分の像が
対応する生成元s=tではφ^n(d)の係数像、別の生成元では零となることを証明した。
次段のqと有限Frobeniusの合成を前段の通常射として使い、
pの消滅をNat.cast保存で確認して有限δ偏微分公式を反復した。
自己生成元・別生成元の公開版、さらにq(C(d))=0なら最高偏微分が
すべて零になる版を証明した。最後の版は基底Frobenius公式を反復する。
CharP・非零性・完備性・有限商のδ構造・p正則性を要求しない。
4公開定理の対象2082ジョブ、pure B4全公開宣言監査成功。
全体4655ジョブ成功。標準3公理のみ。新sorry・公理・引用なし。
有限δ像の一般偏微分公式はdcdb980で先に個別コミット済み。

次のBS専用予定`DeltaDivisionFiniteTopCoefficient.lean`で、
最高係数の一般公式に今回の全段最高偏微分を適用する。
目標は、r_(n+1)を最高変数分離・係数p商で表したときのX_s係数が、
s=tでは初期係数環のφ^(n+1)(d)の像、別の生成元では零になること。
既証明のtotalDegree≤1もこの全反復関係式へ適用する。
その後、係数のd商を加えて最高変数係数が零になることを確認し、
全段の関係式から新しい最高変数を除く具体的な表示へ接続する。
全段のモニック三角形表示・実完備化/perfectionの完全忠実平坦性、
必要な根付きperfectoid拡大と一般B4の引用解消は未実装。

全段最高係数の次のBS専用予定：`DeltaDivisionFiniteGeneratorResidue.lean`で、
初期係数p商をさらにdの係数像で割る具体的な係数商と多項式を構成する。
p,dを消す係数射の下でφ^m(d)の像が零であることから、全最高変数係数の
消滅を証明し、係数写像での次数上界の保存を使って次数1以下も証明する。
係数商にはδ構造を与えない。

## B4-6：全深さの最高変数係数（2026-10-15）

`DeltaDivisionFiniteTopCoefficient.lean`で、深さn+1の実際の関係式を
最高変数分離・係数p商へ送った多項式を定義した。全最高変数係数が
自己生成元ではφ^(n+1)(d)の係数像、別の生成元では零であること、
全最高変数のtotalDegreeが1以下であることを証明した。
CharP・非零性・有限商のδ構造・完備性を要求しない。
6公開宣言の対象2088ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
全段のモニック表示・完備化/perfectionの完全忠実平坦性と一般B4は未実装。

## B4-6：係数の(p,d)商での全最高係数消滅（2026-10-15）

`DeltaDivisionFiniteGeneratorResidue.lean`で、最高変数分離の初期係数p商を
さらにdの係数像で割り、そこへ全反復関係式を送る具体的な多項式を定義した。
この係数商でφ^m(d)の像が全mで零、全最高変数係数が零、
最高変数全体のtotalDegreeが1以下であることを証明した。
係数商のδ構造・非零性・CharP・完備性を要求しない。5公開宣言の対象2089ジョブ成功。
pure B4全公開宣言監査成功。全体4658ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
全段モニック表示と一般B4は未実装。

次のBS専用予定`DeltaDivisionFiniteGeneratorConstant.lean`で、
次数1以下と全一次係数消滅からこの多項式が定数になることを証明する。
既存Finsuppの次数・sum_eq_one_iffと多項式係数APIを使い、
特徴pで偏微分消滅だけから定数性を推論しない。

## B4-6：全段の最高変数除去（2026-10-15）

`DeltaDivisionFiniteGeneratorConstant.lean`で、全反復関係式の(p,d)係数商への
像が定数多項式になることと、そのtotalDegreeが零であることを証明した。
最高変数を零にした初期有限変数の多項式を具体的に定義し、
定数多項式の係数がこの初期多項式の係数商像に一致することを証明した。
次数1以下と全一次係数消滅を使い、標数pで偏微分消滅だけを使う推論を避けた。
4公開宣言の対象2090ジョブ、pure B4全公開宣言監査成功。
全体4658ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
前二単位は95d7c61、7453279で個別コミット済み。

次は、この初期多項式を既存の低次関係式でも割ったときの、
最上位の残る変数についてのモニックp乗方程式を全深さで証明する。
その係数の単元性にはdistinguished d（δ(d)単元）を使う。
今回の最高変数除去だけではモニック性・全段平坦性はまだ従わない。
実完備化/perfectionの完全忠実平坦性と根付きperfectoid拡大、
一般B4の既存André引用解消は未実装。

全段モニック帰納の次のBS専用予定：`RelativeFreeFiniteDeltaPerturbation.lean`。
有限段の商にはδ構造を与えず、次段の通常射qがp,dを消すときの
δ_step(f+p*g+C(d)*h)の像を計算する。p倍の項は包含gの像のp乗、
d倍の項はq(C(δd))と包含hの像のp乗の積を加える。
既存有限δ積・加法剰余公式とδ(p)剰余公式を再利用する。
全段最高変数除去で得た代表元を正規化し、p乗項の単元係数を追う工程で使う。

次のBS専用予定`RelativeFreeFiniteDeltaSquareCongruence.lean`では、
通常射qの初期包含との合成の核Iについて、q(p)=0の下で
f-g∈I²ならq(δ_step f)=q(δ_step g)を証明する。
既存δ環のI冪評価は再定義せず、有限δ計算が環の自己写像でないことに
対応する式だけを有限加法・積公式とイデアル積帰納法で証明する。
正規化の二次誤差を無視できることを全有限段のモニック帰納で使う。

## B4-6：有限δ計算のp倍・d倍代表元補正（2026-10-15）

`RelativeFreeFiniteDeltaPerturbation.lean`で任意通常射q（q(p)=q(Cd)=0）について
δ_step(p*g)の像が包含gの像のp乗、δ_step(Cd*h)の像が
q(Cδd)と包含hの像のp乗の積になることを証明した。
δ_step(f+p*g+Cd*h)の像にこれら二つの項が加わる式も証明した。
既存有限δ剰余・積・加法公式を使用した。係数商のδ構造・非零性は不要。
3公開定理の対象2071ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
全段の正規化帰納とモニック表示は引き続き未実装。

## B4-6：有限δ計算の二次誤差除去（2026-10-15）

`RelativeFreeFiniteDeltaSquareCongruence.lean`で、次段からの通常射q
（q(p)=0）と初期包含の合成の核Iについて、f∈I²ならq(δ_step f)=0、
f-g∈I²ならq(δ_step f)=q(δ_step g)を証明した。
有限δ計算は環の自己写像でないため、既存自己δ環のイデアル冪評価を
そのまま適用せず、有限積・加法公式と既存イデアル積帰納法を使った。
さらに、fとr+p*g+Cd*hの差がI²に属す具体的な正規形から
δ_step fの像を二つのp乗補正項で計算する公開定理を証明した。
3公開定理の対象2072ジョブ、pure B4全公開宣言監査成功。
全体4660ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
p,d代表元補正は687650fで個別コミット済み。

残る全段正規化で要るのは、単にmod(p,d)で最高変数が消えることではなく、
δを一段適用する前の関係式について核の二乗まで追った正規形である。
その正規形を全深さで構成する帰納法は未実装。最高係数公式だけから
次の残存変数のp乗係数・単元性を断定しない。
Witt全係数の三角形積公式はMathlib/MulCoeff.leanにあるが、
現在のδ構造（WittTwo断面）からその全係数比較へ渡すAPIは未確認。
既存の二段目モニック表示は維持する。全段表示・全段平坦性、
実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

次のBS専用予定`RelativeFreeFiniteDeltaSubtraction.lean`で、任意次段イデアルIに
初期包含f,gが属すとき、δ_step(-g)+δ_step(g)と
δ_step(f-g)-(δ_step(f)-δ_step(g))がI²に入ることを証明する。
既存Witt加法補正項の平方所属と有限δ加法公式を再利用する。
`DeltaDivisionFirstOrderNormalForm.lean`では、第一反復関係式の具体的正規形
Cφ(d)*X₁+Cδ(d)*X₀^p-Cδ(a)からの差がI²に属すことを証明する。
初期包含d*x,aの消滅を仮定し、pの正則性・有限商のδ構造は要求しない。
これを全段正規化の初期段とする。

## B4-6：有限δ減算の二次誤差（2026-10-15）

`RelativeFreeFiniteDeltaSubtraction.lean`で、任意次段イデアルIについて
入力の包含像がIに属せば有限δの符号誤差がI²に入り、
二入力の包含像がIに属せば減算誤差もI²に入ることを証明した。
有限δ加法公式と既存Witt補正項の平方所属を再利用した。
p∈I・p正則性・有限商のδ構造を要求しない。
2公開定理の対象2073ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
次は第一反復関係式の具体的正規形へ適用する。

## B4-6：第一反復関係式の二次誤差付き正規形（2026-10-15）

`DeltaDivisionFirstOrderNormalForm.lean`で任意有限段の基底係数倍について
δ_step(Cd*f)=Cφ(d)*δ_step(f)+Cδ(d)*incl(f)^pを正確に証明した。
Cd,Caを含む任意次段イデアルIについて、通常除算関係式のδ像と
この式からCaのδ像を引いた正規形の差がI²に入ることを証明した。
実際の第一反復有限関係式を
Cφ(d)*X₁+Cδ(d)*X₀^p-Cδ(a)へ二次誤差付きで置き換えた。
p∈I・p正則性・有限商のδ構造・非零性を要求しない。
次段の通常射qがp,d,aを消す場合には、第一段の具体的正規形へ
有限δを適用して実際の第二反復関係式のq像を計算できることも証明した。
これは正規形からの差が初期包含とqの合成の核の二乗に入ることを使う。
4公開定理の対象2083ジョブ、pure B4全公開宣言監査成功。
全体4661ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
有限δ減算誤差は8f3deb4で個別コミット済み。

正規形の初期段と次段への使用は証明済みだが、全深さの正規形は未実装。
次の帰納では、前段の誤差がI²というだけではそのδ像はIまでしか
制御できず、さらに次のδにそのまま捨てられない点を追う必要がある。
高次イデアル冪まで追う正規形か、Witt全係数の三角形比較が候補。
単に二次誤差を各段で捨てる帰納法は未採用である。
全段モニック表示・全段平坦性・実完備化/perfectionの完全忠実平坦性、
引用なしの根付きperfectoid拡大と一般B4は引き続き未実装。

次のBS専用予定`RelativeFreeFiniteDeltaAdicEstimate.lean`では、次段イデアルJに
pが属すとき、初期包含の逆像Iについてf∈I^(m+1)ならδ_step(f)∈J^mを
全mで証明する。既存自己δ環の評価を再定義せず、有限δ計算が異なる環へ
進むための評価だけを既存の有限積・加法公式、イデアル積帰納法、
Witt補正項のイデアル所属と包含射のcomap冪評価で証明する。
二代表元の差がI^(m+1)ならδ像の差はJ^mとなる版も証明し、
全段正規化で誤差冪の損失を追う工程で使用する。

次のBS専用予定`RelativeFreeFiniteDeltaIterate.lean`では、初期N+1段から
k回の有限δ計算を繰り返し、初期N+k+1段へ置く具体的な多項式を定義する。
相対自由δ環への標準包含の像が実際のδ^k像であることを証明する。
相対自由環のイデアルJにpが属す場合、最初の誤差がJ^(m+k)なら
k回の有限δ計算後の誤差がJ^mに入ることを既存自己δ環の一段評価で反復する。
全段正規化で必要な誤差冪の予算を明示する。

## B4-6：異なる有限段の間の全冪δ評価（2026-10-15）

`RelativeFreeFiniteDeltaAdicEstimate.lean`で任意次段イデアルJ（p∈J）と
初期包含の逆像Iについて、δ_step(I^(m+1))⊆J^mを全mで証明した。
同じ仮定で、摂動および二代表元の差の評価も証明した。
有限積・加法公式、既存イデアル積帰納・comap冪評価、
Witt補正項のイデアル所属を再利用した。
有限生成性・正則性・完備性・有限商のδ構造を要求しない。
3公開定理の対象2060ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
次に実際の全反復δ計算との比較を行い、k回後の誤差冪を追う。

## B4-6：全有限δ反復と誤差冪の予算（2026-10-15）

`RelativeFreeFiniteDeltaIterate.lean`で初期N+1段の任意多項式へk回の
有限δ計算を適用し、初期N+k+1段の多項式にする具体的な反復を構成した。
零・後続の式と、標準包含の像が実際の相対自由δ環のδ^k像になることを証明した。
相対自由環のJにpが属し、最初の二代表元の誤差がJ^(m+k)に属す場合、
k回後の包含像の誤差はJ^mに属すことを、既存自己δ環の一段評価で反復した。
新しい一般δ冪評価を共通層へ重複作成していない。
5公開宣言の対象2061ジョブ、pure B4全公開宣言監査成功。
全体4663ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
一段の有限δ全冪評価はd5df574で個別コミット済み。

全段正規化には、必要な残り反復回数kに応じたJ^(m+k)精度の
具体的な正規形を実際の関係式について構成する工程が残る。
今回の誤差評価は、その正規形の存在を仮定なしで与えるものではない。
全段モニック表示と平坦性、実完備化/perfectionの完全忠実平坦性、
引用なしの根付きperfectoid拡大と一般B4は未実装。

次のBS専用予定`WittDivisionTriangular.lean`で、MathlibのnthRemainder、
Verschiebung積公式とFrobenius係数公式を使い、pを消す任意係数環Rについて
x.coeff 0=0のWitt除数xの積(x*y).coeff(n+2)を、
x.coeff 1^(p^(n+1))*y.coeff(n+1)^pと下位y係数だけの剰余関数に分離する。
x.coeff 1が単元なら、その積係数の方程式をモニックp乗方程式にする。
零環はSubsingletonの場合として含め、MathlibのCharP仮定を無条件に要求しない。
反復δ座標とWitt座標の比較は未実装であり、この計算だけでは
既存δ除算包の全段表示が完成したとはしない。

## B4-6：Witt除算の全深さ三角形公式（2026-10-15）

著者版Prop3.13（pp33–35）は導来pushoutとCor2.44・2.39を使い、
現在のδ二次誤差の帰納だけでは全段表示を与えないことを再確認した。
`WittDivisionTriangular.lean`で、pを消す任意係数環R、
x∈WittVector p R、x.coeff 0=0、任意nについて、
(x*y).coeff(n+2)=x.coeff 1^(p^(n+1))*y.coeff(n+1)^p+r(yの下位n+1係数)
となる下位係数だけの剰余関数rの存在を証明した。
第1係数の指定単元uから、全段の積係数=cと具体的な
モニックp乗多項式の根条件の同値を証明した。零環も含む。
MathlibのnthRemainder・Verschiebung積公式・Frobenius係数公式を再利用した。
2公開定理の対象2055ジョブ、pure B4全公開宣言監査成功。
全体4664ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。

反復δ座標との比較は未実装。次の比較候補は、p乗算が単射のδ環Aに
f:A→WittVector p Aを構成し、ghostComponent n(f a)=φ^n(a)を全nで示すこと。
このWitt liftの存在は未証明であり、既存WittTwo断面から自動的に
全Witt断面が得られるとは扱わない。比較が得られて初めて、今回の
モニックWitt式を実際のδ除算関係式の有限表示に移す工程へ進める。

### 共通基盤への要求 G4（未送信、2026-10-15）

対象：任意CommRing A、素数p、Function.Injective(fun a:A => (p:A)*a)。
結論：WittVector.ghostMap (p:=p) (R:=A)が単射。
使用：B4-6のδWitt liftの環射性・一意性の比較。
既存APIの不足：Mathlib/WittVectorと既存共有コードを検索した範囲で、
pが単元であるghostEquivとは別の、p乗算単射だけの単射APIを確認できない。
待つ工程：ghost座標一致から全Witt元の一致を出す比較のみ。
独立作業：δから全Witt係数を構成するp可除性、下位座標の三角形比較、
BS専用の今回のWitt除算公式と有限δの誤差評価。
共通Witt補題の重複実装・共通ファイルの編集・他チャットへの送信はしない。
全段モニック表示・平坦性、実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

次のBS専用予定`DeltaWittGhostStep.lean`：既存Mathlibの
dvd_sub_pow_of_dvd_subを再利用し、δ構造DのFrobenius合同をp乗反復で強める。
φ^n(a)=Σ_(i≤n) p^i*b_i^(p^(n-i))という前段のghost等式を仮定すると、
次段のφ^(n+1)(a)から既定係数の部分和を引いた差がp^(n+1)で割り切れる
ことと、次のghost係数の存在を証明する。p正則性はこの存在段階では不要。
B4-6のδから全Witt liftの係数構成で使い、G4単射比較を待たずに進める。

次のBS専用予定`DeltaWittGhostCoefficients.lean`では、前段ghost係数の延長
を選択して既定の係数を保存する有限prefixを構成し、整合性を証明する。
対角列b_nから全nのghost等式を満たす具体的な係数列を構成する。
係数列の存在にはp正則性やG4を要求せず、環射性・一意性は別工程とする。

## B4-6：δFrobeniusから次のWitt ghost係数の存在（2026-10-15）

`DeltaWittGhostStep.lean`で既存Mathlib/dvd_sub_pow_of_dvd_subを再利用し、
φ(a)とa^pのp合同をp^k乗後のp^(k+1)可除性へ強めた。
前段のghost等式φ^n(a)=Σ_(i≤n)p^i*b_i^(p^(n-i))から、
φ^(n+1)(a)と既定係数部分和の差がp^(n+1)で割り切れることを証明した。
これから次のghost係数の存在を証明した。p正則性・完備性は不要。
3公開定理の対象2052ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
全係数列と実際のWitt元の構成を次に行う。環射性・δ座標比較は未実装。

`DeltaWittGhostCoefficients.lean`の構成範囲に、係数列からの実際の
WittVector p Aの元と、その全ghost成分がφの反復になる比較も含める。
点ごとのWitt元の存在と、環射を構成する工程は区別する。

## B4-6：全ghost係数列と点ごとのWitt元（2026-10-15）

`DeltaWittGhostCoefficients.lean`で既定係数を保存する有限prefixを
選択的に延長し、prefixの全ghost等式・互換性を証明した。
対角列を具体的な全係数列として定義し、全nで
φ^n(a)=Σ_(i≤n)p^i*b_i^(p^(n-i))となることを証明した。
この係数列から実際のWittVector p Aの元deltaWittGhostVector D aを構成し、
全ghost成分がφの反復に一致し、第0係数がaに戻ることを証明した。
p正則性・完備性を存在には要求しない。
6公開宣言の対象2053ジョブ、pure B4全公開宣言監査成功。
全体4669ジョブ成功（既存Inputsのsorry警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
一段係数延長の可除性は0cef6acで個別コミット済み。

点ごとのWitt元の存在は証明済み。環射性と一意性、δ反復座標との
全段三角形比較は未実装であり、全段δ除算包の表示・平坦性の完成とはしない。
G4単射を用いた環射性比較を待つ間、p乗算単射の仮定で第1係数が
δ(a)に一致することなど、座標の比較は独立に進められる。
全段正規化・モニック表示、実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

次のBS専用予定`DeltaWittGhostLowCoefficients.lean`で、p乗算単射の仮定から
構成済みWitt元の第1係数がδ(a)に一致し、長さ2切り詰めが
既存DeltaStructure.sectionHomに一致することを証明する。
既存第1ghost係数公式とpのキャンセルを使い、G4や全Witt環射性は待たない。
次のBS専用予定`DeltaWittGhostRingHom.lean`では、ghostMap単射を明示仮定として
構成済み点ごとのWitt写像の環射性と第0係数射の断面性を証明する。
これはG4を仮定に接続する前は条件付きAPIとして区別する。

## B4-6：全Witt元と既存W₂断面の低次比較（2026-10-15）

`DeltaWittGhostLowCoefficients.lean`で、p乗算単射の仮定のみから
構成済みWitt元の第1係数がδ(a)に一致し、長さ2切り詰めが
既存DeltaStructure.sectionHomに一致することを証明した。
既存第1ghost公式とpキャンセルを使用し、G4を要求しない。
2公開定理の対象2054ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
全Witt環射性の単射仮定の供給と全段座標比較は別工程である。

## B4-6：ghost単射下の全Witt環射と一意性（2026-10-15）

`DeltaWittGhostRingHom.lean`で、ghostMap単射を明示仮定として
構成済み点ごとのWitt写像の環射性を証明した。
各ghost成分がφ^nであり、RingHom冪が環射であることを使用した。
第0係数環射との合成が恒等、p乗算単射下で長さ2切り詰めとの合成が
既存DeltaStructure.sectionHomであること、全ghost成分を指定した環射の
一意性を証明した。4公開宣言の対象2055ジョブ、
pure B4全公開宣言監査成功。全体4672ジョブ成功
（既存Inputsのsorry警告あり）。標準3公理のみ。新sorry・公理・引用なし。
低次座標比較はf393c33で個別コミット済み。

このAPIの環射性・一意性はghostMap単射という明示的な数学的仮定に相対的。
G4からp乗算単射だけのAPIへ接続する工程は未実装であり、
その仮定を既証明・新規引用・公理として供給していない。
p乗算単射だけによるW₂比較は証明済みで、G4の受領を待たない。
全反復δ座標と全Witt座標の三角形比較、全段δ除算包のモニック表示・平坦性、
実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

次のBS専用予定`DeltaWittGhostFrobenius.lean`：ghostMap単射を明示仮定として
構成済みWitt写像が基底φとWitt Frobeniusを絡めることを証明する。
環射の図式とF(lift(a))=lift(a)^p+p*lift(δ(a))を証明し、
任意通常射q:A→BによるWitt係数写像での同式の像も証明する。
終域Bのδ構造・完備性・非零性を要求しない。
全段δ座標比較に使う式であり、G4単射を供給済みとはしない。

次のBS専用予定`DeltaWittGhostCoefficientTwo.lean`：p乗算単射だけの仮定で
第2Witt係数をδ²(a)と下位座標a,δ(a)に由来する補正bに分離する。
補正はp²*b=φ(a)^p-a^(p²)を満たし、既存p乗可除性がその存在を与える。
第2ghost公式とp²キャンセルで座標比較を証明する。G4は使用しない。
全段三角形座標比較へ向けた実際の第2座標の計算である。

## B4-6：全Witt写像のFrobenius図式とδ方程式（2026-10-15）

`DeltaWittGhostFrobenius.lean`で、ghostMap単射を明示仮定として
構成済みWitt元のFrobeniusが基底φの像に一致することと環射の図式を証明した。
そこからF(lift(a))=lift(a)^p+p*lift(δ(a))を証明し、任意通常射q:A→Bの
Witt係数写像での式の像も証明した。Bのδ構造・非零性・完備性は要求しない。
4公開定理の対象2058ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
G4単射仮定に相対的なAPIであり、p正則性だけの仮定へ接続は未実装。

## B4-6：第2Witt係数の三角形比較（2026-10-15）

`DeltaWittGhostCoefficientTwo.lean`で、p乗算単射だけの仮定から
第2Witt係数がδ²(a)+bとなる補正bの存在を証明した。
補正はp²*b=φ(a)^p-a^(p²)を満たし、a,δ(a)だけから決まる。
既存のp乗可除性と構成済み全ghost等式、第1係数比較、p²キャンセルを使った。
この下位座標補正を指定すれば同じ係数式が成り立つ版も証明した。
G4や全ghost射単射、全Witt環射性を要求しない。
2公開定理の対象2055ジョブ、pure B4全公開宣言監査成功。
全体4672ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
Frobenius図式の条件付きAPIは6ac98caで個別コミット済み。

次のBS専用予定`RelativeFreeFiniteFrobeniusIterate.lean`で、有限Frobenius射を
反復する実際の環射と相対自由δ環のφ反復を比較する。
続くBS専用予定`RelativeFreeFrobeniusTopLinear.lean`では、自由初期変数X₀の
φ^n像がp^n*X_nと第n段未満の変数だけの多項式の和であることを全nで証明する。
これはδ反復関係式の最高係数のp剰余とは別の、φ反復の正確な線形表示である。
ghost等式で下位Witt係数が下位変数だけに属すことを帰納すると、
p乗算単射下で第nWitt係数の最高δ変数係数が1となる比較へ使用できる。
この全段比較は未実装。G4を待たずに進める独立作業である。
全段δ除算包のモニック表示・平坦性、完備化/perfectionの完全忠実平坦性、
引用なしの根付きperfectoid拡大と一般B4は引き続き未実装。

最高線形表示の実装順を調整する。`RelativeFreeFrobeniusTopLinear.lean`で
下位多項式だけを既存有限FrobeniusStepで再帰的に構成すれば、
別の一般的有限FrobeniusIterate環射の構成なしに直接全段の表示を証明できる。
`RelativeFreeFiniteFrobeniusIterate.lean`は必要性が確定するまで保留し、
今回は既存FrobeniusStep_imageを再利用して直接、
φ^(n+1)(X₀)=p^(n+1)*X_(n+1)+initialMap(n+1)(lower_n)を証明する。
lower_nは第n段以下の変数しか持たない具体的有限多項式である。

`RelativeFreeFrobeniusTopLinear.lean`の範囲に、自由初期変数のφ^n像を
初期n+1段へ置く具体的有限多項式、その包含像の一致と変数段数上界も含める。
これは全段Witt係数の下位変数所属を追う際の具体的な有限表示である。

次のBS専用予定`RelativeFreeWittGhostRecurrence.lean`で、相対自由δ環の
自由初期変数の構成済みWitt係数b_nを定義し、
p^(n+1)*(b_(n+1)-X_(n+1))=initialMap(lower_n)-
Σ_(i≤n)p^i*b_i^(p^(n+1-i))を全nで正確に証明する。
初期係数b₀=X₀も確認する。全ghost等式と今回のφ最高線形表示を使い、
p正則性・G4・全Witt環射性を要求しない。
下位係数の変数範囲を帰納し、p正則性による最高δ変数係数1の抽出へ使う。

## B4-6：自由Frobenius反復の全段最高線形表示（2026-10-15）

`RelativeFreeFrobeniusTopLinear.lean`で既存有限FrobeniusStepを使って
下位多項式lower_nを再帰的に構成し、任意基底δ環・任意生成元・全nで
φ^(n+1)(X₀)=p^(n+1)*X_(n+1)+initialMap(n+1)(lower_n)を正確に証明した。
φ^n(X₀)を初期n+1段に置く具体的な有限多項式、
包含像の一致と全変数の段数≤nという上界も証明した。
既存の有限Frobeniusの包含図式を再利用し、一般的反復環射の重複構成を避けた。
p正則性・非零性・完備性・G4・全Witt環射性を要求しない。
7公開宣言の対象2059ジョブ、pure B4全公開宣言監査成功。
全体4675ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
全ghost等式へ代入してWitt最高座標との差の再帰式へ接続する。

## B4-6：自由Witt係数と最高δ変数の全段再帰式（2026-10-15）

`RelativeFreeWittGhostRecurrence.lean`で相対自由δ環の初期変数から
構成したWitt係数多項式b_nを定義し、b₀=X₀を証明した。
全ghost等式と正確なφ最高線形表示を使い、全nで
p^(n+1)*(b_(n+1)-X_(n+1))=initialMap(lower_n)-
Σ_(i≤n)p^i*b_i^(p^(n+1-i))を正確に証明した。
任意基底δ環・任意生成元で、p正則性・非零性・G4・環射性は不要。
3公開宣言の対象2062ジョブ、pure B4全公開宣言監査成功。
全体4675ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
φ最高線形表示はc64d6c8で個別コミット済み。

次のBS専用予定`RelativeFreeWittGhostSupport.lean`では、基底のp乗算単射
の仮定で、b_n-X_nの変数が第n段未満だけであることを全nで証明する。
既存supported部分代数と、今回の再帰式、p冪乗算単射による係数の
零判定を使う。NoZeroDivisors・非零性・G4は追加しない。
これから初期n段の有限多項式c_nを取り出し、b_n=X_n+initialMap(n)(c_n)という
最高δ変数係数1の全段三角形表示へ進む。
全段三角形比較と実際のδ除算包の表示・平坦性、実完備化/perfectionの
完全忠実平坦性、必要なperfectoid拡大と一般B4はまだ未実装。

次のBS専用予定`RelativeFreeWittGhostTriangular.lean`で、今回の全段下位変数
所属から既存exists_rename_eq_of_vars_subset_rangeを用い、初期n段の有限
多項式c_nを取り出し、b_n=X_n+initialMap(n)(c_n)を全nで証明する。
具体的なc_nを選択して定義し、表示の一意性と第0段のc₀=0を証明する。
任意基底・任意添字族でp乗算単射以外の仮定は追加しない。
G4や全Witt環射性を待たない、実際の全段三角形座標表示である。

## B4-6：全Witt係数の下位変数所属（2026-10-15）

`RelativeFreeWittGhostSupport.lean`で、基底のp乗算単射だけを仮定し、
全nについてb_n-X_nが第n段未満の変数のsupported部分代数に属すことを証明した。
p冪係数の乗算で多項式係数の零判定が保たれることを内部で示し、
全段再帰式をsupported部分代数の加法・積・冪・和の閉性で強帰納した。
各b_nの変数段数≤nも証明した。NoZeroDivisors・非零性・G4・環射性は不要。
2公開定理の対象2064ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
この所属から具体的な有限下位多項式を取り出す。

## B4-6：全Witt係数の係数1の有限三角形表示（2026-10-15）

`RelativeFreeWittGhostTriangular.lean`で全nの下位変数所属から既存rename APIを
用いて初期n段の有限多項式c_nを取り出し、b_n=X_n+initialMap(n)(c_n)を
任意基底δ環・任意添字族に対して全段で証明した。
具体的なc_nを選択して定義し、標準包含の単射性でその表示の一意性、
第0段のc₀=0も証明した。p乗算単射以外の仮定は追加していない。
NoZeroDivisors・非零性・G4・全Witt環射性を要求しない。
5公開宣言の対象2065ジョブ、pure B4全公開宣言監査成功。
全体4675ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
下位変数所属は34edf12で個別コミット済み。

次のBS専用予定`RelativeFreeWittCoordinateChange.lean`で、X_(s,n)をb_(s,n)へ
送る相対多項式代数射と、c_(s,n)を使った段数の強帰納による逆変数を構成する。
全有限下位多項式は第n段未満しか含まないため、逆変数の評価は前段だけで定義できる。
両合成が係数・変数上で恒等となることを証明し、実際のA代数同型にする。
G4や全Witt環射性を待たずに、現在の全段座標表示から独立に進める。
ただし、実際のδ除算関係式をWitt積方程式へ移す環射比較はG4への接続を含む。
座標同型だけで除算包の全段表示・平坦性を完成したとはしない。
実完備化/perfectionの完全忠実平坦性、根付きperfectoid拡大と一般B4は未実装。

## B4-6：全Witt/δ座標の実際の代数同型（2026-10-15）

`RelativeFreeWittCoordinateChange.lean`でX_(s,n)を構成済みWitt係数b_(s,n)へ
送る相対多項式代数射を定義し、初期n段の下位多項式を前段逆変数で評価して
引く強帰納により逆変数と逆代数射を構成した。
逆射が全Witt係数を元のδ変数へ戻すこと、順射が逆変数をδ変数へ戻すこと、
両合成の恒等性を証明し、実際のA代数同型relativeFreeWittCoordinateEquivを構成した。
各変数上の順逆図式も公開した。任意添字族・零環を含み、基底のp乗算単射
以外の仮定を追加せず、G4・全Witt環射性・完備性を要求しない。
既存aeval・rename・初期包含とNat.strongRecを再利用した。
11公開宣言の対象2066ジョブ、pure B4全公開宣言監査成功。
全体4675ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。

次のBS専用予定`RelativeFreeWittInverseSupport.lean`で逆変数の段数≤nを
強帰納し、逆代数射が各初期有限変数部分代数を保つことを証明する。
有限δ関係式の商へ全Witt座標同型を制限するために使う。
G4を待たずに進める独立作業である。
実際のδ除算反復関係式とWitt積の全係数方程式を対応させる環射比較は
まだ未実装で、G4単射仮定をp正則性から供給する工程も残る。
全段座標同型の完成と、δ除算包の全段モニック商表示・平坦性の完成を区別する。
実完備化/perfectionの完全忠実平坦性、必要なperfectoid拡大と一般B4は未実装。

次のBS専用予定`RelativeFreeFiniteWittCoordinateChange.lean`で、段数<Nの変数
部分代数をσ×Fin Nの通常有限多項式環と同定する。
既存supportedEquivMvPolynomialとrenameEquivを組み合わせ、標準包含との
一致を証明する。制限済みWitt座標同型をこの有限多項式環へ移し、
全座標同型と標準包含の具体的な図式を証明する。
δ商関係式の有限段同型へ使用するが、関係イデアルの一致・平坦性とは別工程。

## B4-6：逆座標の段数と初期変数部分代数への制限（2026-10-15）

`RelativeFreeWittInverseSupport.lean`で逆変数の段数≤nを強帰納し、
全座標同型の順逆射が各初期N段のsupported部分代数を保つことを証明した。
前段逆変数を同部分代数内で評価する既存aevalと、adjoinの生成性を使用した。
任意初期N段のsupported部分代数上の実際のA代数同型を構成し、
全変数環への包含図式も公開した。任意基底・任意添字族・零環を含み、
p乗算単射以外の仮定、G4・全Witt環射性・完備性は要求しない。
6公開宣言の対象2067ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
通常有限多項式環への同定と順逆包含図式へ進む。

## B4-6：通常有限多項式環上のWitt座標同型（2026-10-15）

`RelativeFreeFiniteWittCoordinateChange.lean`で初期変数集合とσ×Fin Nの
標準添字同型、有限多項式環と初期supported部分代数のA代数同型を構成し、
標準包含が既存relativeFreeFiniteInitialPolynomialMapと一致することを証明した。
これで制限済み座標同型をMvPolynomial (σ×Fin N) Aの実際のA代数同型へ移した。
有限同型の順逆と全座標射の標準包含図式、各有限変数の像が
対応するWitt係数である図式を証明した。N=0・任意添字族・零環を含む。
p乗算単射以外の仮定、G4・全Witt環射性・完備性は要求しない。
7公開宣言の対象2068ジョブ、pure B4全公開宣言監査成功。
全体4675ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
逆変数の有限段保存は42ef83cで個別コミット済み。

次のBS専用予定`DeltaWittGhostNaturality.lean`で、δ射f:(A,D)→(B,E)と
終域BのghostMap単射の明示仮定の下、Witt.map f (lift_D a)=lift_E(f a)を証明する。
終域でのghost指定の一意性だけを使い、源のghost単射は点ごとの図式には要求しない。
既存δ射のFrobenius自然性とWitt ghost多項式評価を再利用する。
これは全段三角形表示を、自由変数から実際の除算反復関係式のδjetへ
評価するための比較である。G4は未受領であり、その単射仮定を供給済みとはしない。
関係イデアルの一致・Witt積方程式への比較・全段モニック商表示・平坦性、
実完備化/perfectionの完全忠実平坦性と一般B4は引き続き未実装。

次のBS専用予定`DeltaWittJetComparison.lean`で、p乗算単射のδ環Aと
ghostMap単射の明示仮定から、任意aの第nWitt係数が
δ^n(a)と下位δ反復を有限多項式に評価した補正の和となる式を証明する。
補正の零評価が零であること、任意通常射q:A→Bが下位δjetを消せば
第nWitt係数とδ^n(a)のq像が一致することを証明する。
さらに有限深さの全δjet消滅と全Witt jet消滅の同値へ進む。
終域Bにはδ構造・完備性・非零性を要求しない。
G4から源のghost単射を供給する工程は未実装として区別する。

`DeltaWittJetComparison.lean`に、深さN以下のδjet消滅と、係数射を適用した
Witt元の長さN+1切り詰めが零になることの同値も含める。
次のBS専用予定`DeltaDivisionWittJetRelations.lean`では、この同値と構成済み
全Witt環射性からd*x-aのδjet消滅を切り詰めたWitt積の等式へ移す。
相対自由δ環の実際の反復除算関係式族にも適用する。
p乗算単射と源のghost単射を明示し、終域のδ構造・非零性は要求しない。
G4供給前はghost単射に相対的な成果と明示し、全射性引用解消とは数えない。

## B4-6：δ射に関する全Witt liftの自然性（2026-10-15）

`DeltaWittGhostNaturality.lean`で、δ射f:(A,D)→(B,E)と終域Bの
ghostMap単射を明示仮定として、Witt.map f(lift_D a)=lift_E(f a)を証明した。
全係数の自然性と、両ghost射単射下での全Witt環射の合成図式も公開した。
既存δFrobenius自然性とghost多項式評価、係数写像を再利用した。
点ごとの自然性と係数比較には源のghost射単射は不要。
3公開定理の対象2056ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
G4仮定を供給済みとは扱わず、任意元のδjet評価比較へ進む。

## B4-6：任意元の全有限δjet/Witt jet比較（2026-10-15）

`DeltaWittJetComparison.lean`でp乗算単射と源ghostMap単射を明示仮定として、
任意元の第nWitt係数がδ^nと下位δ反復の有限多項式評価の和であることを証明した。
自由三角形補正の零評価が零、任意通常射qが下位δjetを消せば
第nWitt係数とδ^nのq像が一致すること、深さN以下の全δjet消滅と
全Witt係数消滅、長さN+1のWitt切り詰めの零条件が同値であることを証明した。
終域qの先にはδ構造・非零性・完備性・p正則性を要求しない。
既存相対自由δ評価とWitt切り詰め核判定を再利用した。
5公開定理の対象2070ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
G4が供給すべき源のghost単射には相対的な成果であり、
その仮定を引用・公理として供給していない。
自然性は3bb0879で個別コミット済み。除算Witt積への対応へ適用する。

## B4-6：全有限反復除算関係式とWitt積方程式の同値（2026-10-15）

`DeltaDivisionWittJetRelations.lean`で、p乗算単射と源ghostMap単射を
明示仮定として、任意通常射q:A→Bの下でd*x-aの深さN以下の全δjet
消滅が、長さN+1に切り詰めた係数射適用後のWitt積方程式と同値である
ことを証明した。任意族にも拡張し、相対自由δ環の実際の
deltaDivisionIteratedRelation族へ適用した。
終域Bのδ構造・非零性・p正則性・完備性は要求しない。
既存全Witt環射の積・減算とWitt切り詰め環射を再利用した。
3公開定理の対象2075ジョブ、pure B4全公開宣言監査成功。
全体4684ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
δjet比較は624f0a1、自然性は3bb0879で個別コミット済み。
G4が供給すべき源ghost単射には相対的な成果であり、
その仮定を供給済み・全射性引用解消済みとはしない。

次のBS専用予定`DeltaDivisionWittMonicRelations.lean`で、
q(p)=q(d)=0、δ(d)の像の指定単元、深さn+2以下の除算δjet消滅から、
既証明WittDivisionTriangularを用いて第n+1Witt座標のモニックp乗方程式を
全nで証明する。係数環と源ghost単射の仮定を明示する。
切り詰めの等式から対応する積係数の等式を取り出し、
終域にδ構造・完備性・非零性を要求しない。
ただし、方程式だけから商の同型・全段平坦性は結論しない。
全段モニック商表示・平坦性、実完備化/perfectionの完全忠実平坦性、
必要なperfectoid完全忠実平坦拡大と一般B4は未実装。

## B4-6：実際のδ関係式からの全段Wittモニック方程式（2026-10-15）

`DeltaDivisionWittMonicRelations.lean`で、有限δjet消滅から切り詰めWitt積等式を
取り出し、任意段の積係数が右辺のWitt係数に一致することを証明した。
q(p)=q(d)=0、δ(d)像の指定単元uの下、深さn+2以下の除算δjet消滅から
第n+1Witt座標がモニックp乗方程式を満たすことを全nで証明した。
剰余項は下位n+1座標だけの関数であり、除数・段数を固定すると
任意の被除算元xと右辺aに使える同じ関数を供給した。
distinguished dから同じ単元を取り出して全段に供給する版も証明した。
源p乗算単射と源ghost射単射を明示し、終域のδ構造・非零性・完備性は不要。
3公開定理の対象2083ジョブ、pure B4全公開宣言監査成功。
全体4684ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
G4が供給すべき源ghost単射に相対的な成果であり、全射性引用解消とはしない。

次のBS専用予定`WittDivisionPolynomialRemainder.lean`で、剰余項を
MvPolynomial (Fin(n+1)) Bの実際の下位多項式として構成する。
Mathlib/polyOfInterestの有限変数範囲と既存rename制限を使い、
除数係数を定数、右変数をp乗へ置換した多項式を作る。
この多項式による三角形式を証明し、係数環射での自然性を確認する。
現行の関数rの存在だけでは、通常環射での評価自然性や
有限商の関係イデアル表示を供給済みとはしない。
多項式剰余から実際の全段モニック商表示・平坦性へ接続する必要が残る。
実完備化/perfectionの完全忠実平坦性、根付きperfectoid拡大と一般B4は未実装。

`WittDivisionPolynomialRemainder.lean`に、実際の剰余多項式評価を係数とする
モニックp乗式とWitt積係数等式の同値も含める。
次のBS専用予定`DeltaDivisionWittPolynomialRelations.lean`で、実際のδ関係式
の消滅からこの具体的多項式版の根方程式を導く。
旧関数版の公開APIは維持し、商表示には多項式版と係数射自然性を使う。

`DeltaDivisionWittPolynomialRelations.lean`では、具体的な根多項式を定義し、
下位δjet消滅の下で次のδ関係式の消滅とモニック根条件が同値となる
全段の一歩の比較も証明する。単方向の根方程式だけで商同型と数えない。

## B4-6：Witt除算の具体的下位剰余多項式と自然性（2026-10-15）

`WittDivisionPolynomialRemainder.lean`で既存Mathlib/polyOfInterestを
Fin 2×Fin(n+1)の整数多項式へ制限し、その固定整数多項式を定義した。
除数の係数を定数、右変数をp乗へ置換して
wittDivisionRemainderPolynomial x nを実際のMvPolynomial(Fin(n+1)) Rとして構成した。
pを消す任意Rで、零定数係数除数の第n+2積係数が最高座標のp乗と
この下位多項式の評価の和になることを証明した。零環も含む。
剰余多項式の係数環射による自然性はp消滅・非零性なしで証明した。
指定単元第1係数の下、積係数等式とこの実多項式版のモニック根条件の同値も証明した。
7公開宣言の対象2056ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。G4やδ環の仮定は使用しない。
従来の関数剰余・公開APIは維持し、実際の除算δ関係式の次段へ適用する。

## B4-6：実多項式版の次段δ関係式と根条件の双方向比較（2026-10-15）

`DeltaDivisionWittPolynomialRelations.lean`で、実際の下位剰余多項式を
評価したdeltaDivisionWittRootPolynomialを定義し、モニック性を証明した。
下位δ関係式消滅の下で、次のδ関係式の消滅と次のWitt積係数等式が
同値であることを、Witt切り詰め係数の外延性から証明した。
q(p)=q(d)=0、δ(d)像の指定単元の下、その条件が
この具体的モニック多項式の根条件と同値であることを全段で証明した。
源p乗算単射と源ghost射単射は比較の明示仮定で、
根多項式の定義・モニック性自体にはこれらを要求しない。
終域のδ構造・非零性・完備性は不要。
4公開宣言の対象2085ジョブ、pure B4全公開宣言監査成功。
全体4690ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
実剰余多項式と自然性は9a457f3で個別コミット済み。

次のBS専用予定`DeltaDivisionWittRelationElement.lean`で源の単元uを固定し、
q=idの根多項式を源Witt座標で評価した実際の環元を定義する。
任意通常射qに対してこの環元の像がq先の根多項式評価になる自然性を、
今回の剰余多項式のmap公式・Units.map・Polynomial評価自然性で証明する。
次のBS専用予定`DeltaDivisionWittRelationIdeal.lean`では、任意源イデアルIが
p,dと深さn+1以下の下位除算δ関係式を含む場合に、
I⊔span{δ^(n+2)(d*x-a)}がI⊔span{対応する源Witt根関係元}に一致することを証明する。
既存の有限関係イデアルを再定義せず、その次段置換に使う。
G4単射仮定への接続、全段モニック商表示・平坦性、
実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

`DeltaDivisionWittRelationIdeal.lean`に、任意添字族x_s,a_sの次段δ生成元族を
同時にWitt根関係元族へ置き換えるspan(range ...)のイデアル等式も含める。
添字族の有限性を追加せず、既存有限深さの関係イデアルの後続式へ使う。

## B4-6：源のWitt根関係元と通常射自然性（2026-10-15）

`DeltaDivisionWittRelationElement.lean`で源の指定単元uを使い、
源Witt座標で根多項式を評価した実際の環元を定義した。
任意通常射qによるその像が、u.map qを使ったq先の根多項式評価に一致する
自然性を剰余多項式のmap公式とUnitsの自然性から証明した。
p正則性やG4はこの定義・自然性には不要。
源p乗算単射・源ghost射単射を明示仮定とし、q(p)=q(d)=0と下位δjet消滅の
下で次段δ関係式消滅とこの源の根関係元の像の消滅の同値も証明した。
3公開宣言の対象2086ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
商射へ適用して、下位イデアル上の生成元置換に使う。

## B4-6：下位イデアル上の次段生成元置換（2026-10-15）

`DeltaDivisionWittRelationIdeal.lean`で、p,dと深さn+1以下の下位δ関係式を
含む任意イデアルIについて、次段δ関係式と対応する源Witt根関係元の
所属が同値であることを、商射への零条件比較から証明した。
Iに次段δ生成元を加えたsup-spanが、Witt根関係元を加えたものに一致する
正確なイデアル等式を証明した。任意添字族の生成元を同時に置き換える
span(range ...)版も証明し、有限生成性・Noether性を追加していない。
源p乗算単射・源ghost射単射は明示仮定。完備性や商のδ安定性は不要。
3公開定理の対象2087ジョブ、pure B4全公開宣言監査成功。
全体4693ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
源関係元と自然性は62d2c8cで個別コミット済み。

次のBS専用予定`DeltaDivisionWittFiniteRelationIdeal.lean`で、既存
deltaDivisionFiniteRelationIdealの後続式を今回の族版へ適用する。
(p,Cd)の係数イデアルと既存の深さn+1以下の有限関係イデアルを下位Iとし、
深さn+2への増分が対応するWitt根関係元族のspanになることを証明する。
既存有限イデアルを再定義せず、元の定義からの具体的な全段比較を供給する。
その後、有限Witt座標同型の逆射で根関係元を最高変数のモニック冪式へ
移す表示を、係数射自然性と基底係数上のWitt比較を用いて構成する。
G4への接続、全段モニック商同型・平坦性、完備化/perfectionの
完全忠実平坦性、必要なperfectoid拡大と一般B4は引き続き未実装。

`DeltaDivisionWittFiniteRelationIdeal.lean`では、相対自由環の根関係元族と
その初期N段spanを具体的に定義し、零段・後続式を証明する。
既存の実際の有限δ関係イデアルに加えた(p,Cd)イデアルが、
既存第一剰余イデアルと初期N段Witt根関係元spanの和になる全段式まで進める。
既存δ有限イデアル・第一剰余イデアルを再定義せず再利用する。

次のBS専用予定`RelativeFreeWittCoefficientNaturality.lean`で、相対自由環の
ghostMap単射の明示仮定から、基底係数Caの全Witt元・全係数が
Witt.map Cによる基底Witt像であることを証明する。
逆座標射が基底係数の全Witt係数とWitt元を固定することも証明し、
実際の源根関係元を最高変数のモニック式へ移す計算に使う。
基底p乗算単射は逆座標射の構成にのみ要求し、基底ghost単射は要求しない。

## B4-6：実際の有限δ関係イデアルの全段Witt生成元表示（2026-10-15）

`DeltaDivisionWittFiniteRelationIdeal.lean`で相対自由環の具体的根関係元族と
初期N段のspanを定義し、零段・後続式を証明した。
既存deltaDivisionFiniteRelationIdealの後続式に任意族の生成元置換を適用し、
(p,Cd)を加えた深さn+2の実際の有限δイデアルが、深さn+1のものに
第n根関係元族を加えて得られることを証明した。
これを反復し、全Nで実際の深さN+1イデアルが既存第一剰余イデアルと
初期N段Witt根関係元spanの和に一致することを証明した。
既存δ有限イデアル・第一剰余イデアルの定義は維持・再利用した。
源の相対自由環のp乗算単射・ghost単射を明示仮定とし、添字族の有限性、
商のδ安定性・完備性・非零性は追加していない。
6公開宣言の対象2102ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ。新sorry・公理・引用なし。
座標同型の逆射で具体的な根関係元をモニック式へ移す工程へ進む。

## B4-6：基底Witt係数の相対自然性と逆座標射での固定（2026-10-15）

`RelativeFreeWittCoefficientNaturality.lean`で相対自由環のghost単射を
明示仮定として、基底係数Caの全Witt元と各係数がWitt.map Cによる
基底Witt像に一致することを証明した。基底ghost射単射は要求しない。
逆座標射が基底係数の全Witt係数・Witt元を固定することを証明した。
基底p乗算単射は逆座標射の構成の仮定としてのみ用いた。
既存係数δ射の自然性、Witt係数写像、A代数射の係数可換性を再利用した。
4公開定理の対象2070ジョブ、pure B4全公開宣言監査成功。
全体4696ジョブ成功（共有側の既存警告あり）。
標準3公理のみ。新sorry・公理・引用なし。
実際の有限δイデアルの全段表示は9f17f28で個別コミット済み。

次のBS専用予定`DeltaDivisionWittNormalizedRelation.lean`で、
相対Witt根関係元に逆座標射を適用した像が
X_(s,n+1)^p-C(u^-1)^(p^(n+1))*(C(基底右辺Witt係数)-下位剰余多項式評価)
という正確なモニック形になることを証明する。
基底係数の固定と逆射のWitt変数上の図式、根関係元のmap自然性を用いる。
初期n+2段の具体的な有限多項式と包含図式も構成し、下位係数を
初期n+1段の多項式として分離して最高変数のモニック冪形を示す。
その後、全段イデアル表示を有限座標同型でこの生成元族へ移す。
G4単射仮定への接続、実際の全段商同型と平坦性、
完備化/perfectionの完全忠実平坦性と一般B4は引き続き未実装。

## B4-6：逆Witt座標での具体的有限モニック関係式（2026-10-15）

`DeltaDivisionWittNormalizedRelation.lean`で、初期n+1段に属する具体的な
下位係数多項式と、最高有限変数のp乗からその包含像を引く関係式を定義した。
相対自由環の実際のWitt根関係元の逆座標像が、この有限多項式の包含像に
一致することを証明した。最高変数分離同型での像も
X_s^p-C(下位係数)に一致する。下位係数と有限関係式の包含図式も証明済み。
基底p乗算単射・相対自由環ghost射単射は逆座標像の一致で明示仮定とし、
モニック式自体の定義・包含・変数分離にこれらの仮定は不要。
6公開宣言の対象2106ジョブ、pure B4全公開宣言監査、全体4696ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
一般B4の全射性はまだ未完成であり、André引用の解消とは数えない。

次のBS専用予定`DeltaDivisionWittNormalizedIdeal.lean`で、
初期N段の正規化モニック生成元の通常イデアルを構成する。
逆座標射による既存Witt根関係イデアルのmapが、このspanに一致することを
証明し、既存の全段有限δイデアル等式へ適用する。
最初の剰余イデアルの像を残した段階の正確なmap等式を先に供給し、
その第一段の固定・有限段商表示・平坦性へ接続する。
G4への接続、実際の全段商同型と平坦性、完備化/perfectionの
完全忠実平坦性と引用なし一般B4は引き続き未実装。

## B4-6：全有限δイデアルの逆座標像と第一段の固定（2026-10-15）

`DeltaDivisionWittNormalizedIdeal.lean`で具体的モニック有限関係式の包含像の
初期N段spanを定義した。逆Witt座標射による既存Witt根関係イデアルのmapが
このspanと一致することを証明し、既存の全段有限δイデアル式へ適用した。
さらに逆射が基底係数と初期変数X_(s,0)を固定することから、既存第一剰余
イデアルのモニック表示を用いて第一剰余イデアル自体の固定を証明した。
従って(p,Cd)を加えた実際の深さN+1有限δイデアルの逆座標像は、
第一剰余イデアルと具体的モニック関係元族のspanの和に一致する。
基底・相対自由環のp乗算単射、相対自由環ghost射単射を明示仮定に維持した。
第一剰余の固定にはghost単射は不要。既存イデアルは再定義していない。
5公開宣言の対象2108ジョブ、pure B4全公開宣言監査成功。
標準3公理のみ、新sorry・公理・引用なし。
直前の有限モニック関係式はc0018c0で個別コミット済み。

次のBS専用予定`DeltaDivisionWittNormalizedQuotient.lean`では、このmap等式と
既存の相対Witt座標同型から実際の有限δ剰余商と正規化イデアルの商との
具体的環同型を構成する。標準商射との図式と基底係数の像も証明する。
この商同型自体を全段平坦性の完成とは数えない。
G4への接続、有限段の反復モニック商表示・平坦性、実完備化/perfectionの
完全忠実平坦性と引用なし一般B4は未実装。

## B4-6：実際の有限δ剰余商の具体的正規化環同型（2026-10-15）

`DeltaDivisionWittNormalizedQuotient.lean`で、(p,Cd)を加えた実際の深さN+1
有限δイデアルの商と、第一剰余イデアルおよび具体的モニック関係元族の
spanの和の商を結ぶ環同型を構成した。既存相対Witt座標同型の逆射と
直前の正確なmap等式を使い、商同型一般論はMathlibを再利用した。
標準商射への適用が逆Witt座標射の商像に一致する図式と、
基底係数Caの像を固定することも証明した。
基底・相対自由環p乗算単射、相対自由環ghost射単射は明示仮定。
3公開宣言の対象2109ジョブ、pure B4全公開宣言監査、全体4696ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
全段イデアルの正規化と第一段の固定は067966aで個別コミット済み。
この環同型は全段平坦性・完備化・一般B4の全射性をまだ供給しない。

次のBS専用予定`DeltaDivisionFiniteNormalizedPresentation.lean`で、
初期N+1変数だけの多項式環に第一段と初期N段の正規化関係式を置いた
具体的有限イデアルを構成する。無限相対自由環への包含によるmapが
既存第一剰余イデアルとdeltaDivisionFiniteNormalizedWittIdealの和と
一致することを示す。後続の最高変数分離では、前段イデアルの係数拡張と
X_s^p-C(前段係数)の族を添加した表示を証明する。
これを既存MonicPowerFamilyCoverの商同型・自由性へ接続し、
有限段から全段への平坦性へ進む。Noether性・添字族有限性は追加しない。
G4単射仮定への接続、実完備化/perfectionの完全忠実平坦性と
引用なし一般B4は引き続き未実装。

## B4-6：正規化イデアルの初期有限変数表示（2026-10-15）

`DeltaDivisionFiniteNormalizedPresentation.lean`で、第nモニック関係式を
初期N+1変数の環へ標準renameで置いた具体的生成元を構成した。
第一段の係数・モニック冪関係式と初期N段生成元で生成する有限イデアルを
定義し、無限相対自由環への包含によるmapが既存第一剰余イデアルと
初期N段の正規化イデアルの和に一致することを証明した。
有限生成元の包含図式も証明済み。この有限表示自体にはp正則性・
ghost射単射・完備性・添字族の有限性は不要で、u=δdのみが第一段比較で必要。
4公開宣言の対象2110ジョブとpure B4全公開宣言監査成功。
標準3公理のみ、新sorry・公理・引用なし。
商同型は1e08c2cで個別コミット済み。

次のBS専用予定`DeltaDivisionFiniteNormalizedStep.lean`で、有限生成元の
castSuccによる包含整合性と最上段生成元の具体式を証明する。
前段有限イデアルの標準包含mapと第Nモニック関係式族のspanの和が
次段有限イデアルに一致する後続式を構成する。
最高変数分離後に前段係数イデアルの拡張とモニック冪族として表し、
商射を前段商上のMonicPowerFamilyCoverへ接続する。
この後続式と商表示ができるまで全段平坦性は未実装として扱う。
G4、実完備化/perfectionの完全忠実平坦性と引用なし一般B4も未実装。

## B4-6：有限正規化イデアルの後続式と最高変数分離（2026-10-15）

`DeltaDivisionFiniteNormalizedStep.lean`で、有限生成元のcastSucc包含整合性と
最上段生成元が第Nモニック関係式そのものであることを証明した。
任意添字族の生成元spanの後続式を示し、第一段の係数・初期変数関係を
標準包含で移して、次段有限イデアルが前段のmapと第N関係式族spanの和に
一致することを証明した。最高変数分離同型によるこのイデアルのmapが、
前段イデアルのCによる係数拡張とX_s^p-C(前段係数)のspanの和になる式も
証明した。全て具体的有限環・写像・イデアルを持つ公開定理。
p正則性、ghost射単射、u=δd、添字有限性、Noether性、完備性は不要。
5公開定理の対象2111ジョブ、pure B4監査、全体4699ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
有限表示は11563d6で個別コミット済み。

次のBS専用予定`DeltaDivisionFiniteNormalizedPowerEquiv.lean`で、既存
monicPowerFamilyBaseQuotientEquivを用い、次段有限正規化商が前段商上の
具体的MonicPowerFamilyCoverに同型であることを構成する。
有限正規化商の型は既存有限イデアルの商のabbrevとして置き、
係数は既存下位多項式の前段商像を使う。包含像と最高変数上の図式も証明する。
その同型を前段商上の代数同型として整え、既存自由性・忠実平坦性を移す。
G4への接続、全段平坦性、実完備化/perfectionの完全忠実平坦性と
引用なし一般B4は未実装。

## B4-6：次段有限商の前段商上モニック冪根添加同型（2026-10-15）

`DeltaDivisionFiniteNormalizedPowerEquiv.lean`で既存有限イデアルの商の型を
abbrevとして置き、次段の根係数を既存下位多項式の前段商像として定義した。
最高変数分離と既存monicPowerFamilyBaseQuotientEquivを合成し、
次段有限正規化商が前段商上の具体的MonicPowerFamilyCoverと同型である
ことを構成した。標準包含の商像を係数射に送り、最高変数の商像を
指定p乗根に送る図式も証明した。
p正則性、ghost射単射、u=δd、添字族の有限性、Noether性、完備性は不要。
5公開宣言の対象3240ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。有限イデアル後続式は7522f49で個別コミット済み。
直前の全体ビルドは共有側変更に伴い4699ジョブだった。

次のBS専用予定`DeltaDivisionFiniteNormalizedStepFlat.lean`で、
この同型から前段商と次段商の具体的環射・代数構造を置く。
その環射が元の有限多項式環の標準包含の商像に一致することを証明し、
代数同型によって既存モニック根添加環の自由性・忠実平坦性を移す。
従って単なる非標準の輸送構造ではなく、指定した商射に関する性質として
公開する。さらに全段に進むため有限商間の射を合成する。
G4への接続、全段平坦性、実完備化/perfectionの完全忠実平坦性と
引用なし一般B4は未実装。

## B4-6：標準有限商の一段射の自由性・忠実平坦性（2026-10-15）

`DeltaDivisionFiniteNormalizedStepFlat.lean`で前段商から次段商への具体的環射と
その代数構造を定義した。根添加同型の逆射と係数射の合成で構成し、
その射が元の有限多項式環の標準包含の商像に一致することを証明した。
同型をこの標準一段射に関する前段商代数同型へ整え、既存根添加環の
自由性、平坦性、零商も含む忠実平坦性を移した。
忠実平坦性から標準一段射の単射性も証明し、前段の元が追加で消えない
ことを具体的な通常射について公開した。
p正則性、ghost射単射、u=δd、添字族有限性、Noether性、完備性は不要。
8公開宣言の対象3242ジョブ、pure B4監査、全体4699ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
次段商の根添加表示は019bccfで個別コミット済み。
これで全有限段の隣接射の忠実平坦性は完成したが、適切な共通係数商上の
全有限段・全段極限の平坦性と実完備化/perfectionへの接続は未完成。

次のBS専用予定`DeltaDivisionFiniteNormalizedTowerMaps.lean`では、
標準一段射を合成して任意の後段への具体的射を構成する。
有限多項式環の標準rename包含と商射に両立すること、零段・後続式・合成式、
単射性を証明する。直系の代数構造と全有限段の平坦性へ接続するための
実際の射の系として供給し、既存の一般直極限APIを再利用する。
G4、全段極限の平坦性、実完備化/perfectionの完全忠実平坦性と
引用なし一般B4は引き続き未実装。

## B4-6：任意有限段間の標準商射の直系（2026-10-15）

`DeltaDivisionFiniteNormalizedTowerMaps.lean`で、標準一段射をNat.leRecで
反復して任意n≤mの有限正規化商間の環射を構成した。
恒等・後続式・任意三段での合成式、全ての射の単射性を証明した。
元の有限多項式環の標準rename包含も具体的に定義し、商射とこの包含が
任意二段間で可換になることを証明した。一般直系の型や極限は再定義しない。
p正則性、ghost射単射、u=δd、添字有限性、Noether性、完備性は不要。
7公開宣言の対象3243ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。一段射の忠実平坦性はbaa98d3で個別コミット済み。

次のBS専用予定`DeltaDivisionFiniteNormalizedTowerFlat.lean`で、
任意n≤mの標準商射による代数構造を置き、射の後続式が
IsScalarTowerの係数可換性を保証することを示す。
既存Module.FaithfullyFlat.transを用いた帰納法で、任意二段間の
忠実平坦性と平坦性を証明する。商環・射は今回のものを再利用する。
その後、適切な係数商との初期段比較と直系極限へ進む。
G4、全段極限の平坦性、実完備化/perfectionの完全忠実平坦性と
引用なし一般B4は未実装。

## B4-6：任意二段間の標準有限商射の忠実平坦性（2026-10-15）

`DeltaDivisionFiniteNormalizedTowerFlat.lean`で、任意n≤mの標準商射による
代数構造を置いた。後続一段に関するIsScalarTowerを射の後続式から
証明し、既存Module.FaithfullyFlat.transを使った帰納法で任意二段間の
忠実平坦性と平坦性を証明した。同じ段への射は既存恒等式を用い、
加群構造まで恒等射のものへ簡約して扱った。
零商も含み、p正則性・ghost射単射・u=δd・添字有限性・Noether性・
完備性は仮定していない。直系の商環・写像は再利用した。
4公開宣言の対象3244ジョブ、pure B4監査、全体4699ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
標準射の直系は637ac65で個別コミット済み。
これで任意二段間の忠実平坦性は完成したが、適切な係数商上の全段極限と
実際の完備化/perfectionの完全忠実平坦性、一般B4は未完成。

次のBS専用予定`DeltaDivisionFiniteNormalizedInitialPowerEquiv.lean`で、
初期変数σ×Fin 1をσと同一視し、零段有限正規化イデアルを既存
第一係数多項式イデアルdeltaDivisionFirstPolynomialIdealに移す。
初期有限商と既存DeltaDivisionFirstPowerCoverの具体的同型を構成し、
基底係数と初期変数上の標準商射図式を証明する。
次に既存の適切な係数商A/(p,d,a_s)上の自由性・忠実平坦性を初期有限商へ
移し、今回の任意二段間の忠実平坦性と合成する。
全段極限への比較はこの適切な係数商を使い、元のAや任意商B上の
平坦性を誤って主張しない。G4への接続と実完備化/perfectionの
完全忠実平坦性、引用なし一般B4は引き続き未実装。

## B4-6：初期有限商と適切な係数商上の根添加環の比較（2026-10-15）

`DeltaDivisionFiniteNormalizedInitialPowerEquiv.lean`で、σ×Fin 1とσの
既存prodUnique同値による変数rename代数同型を使い、零段有限正規化
イデアルのmapが既存deltaDivisionFirstPolynomialIdealと一致することを
証明した。初期有限商と既存DeltaDivisionFirstPowerCoverの具体的環同型を
構成し、基底係数と初期変数の標準商像の図式を証明した。
基底係数は適切な係数商A/(p,d,a_s)の係数射、初期変数は指定p乗根へ送る。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
5公開宣言の対象3248ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。任意二段間の忠実平坦性はb6dcf7eでコミット済み。

次のBS専用予定`DeltaDivisionFiniteNormalizedInitialFlat.lean`で、
適切な係数商から初期有限商への具体的環射・代数構造と基底係数上の図式を
構成する。初期比較をこの射に関する代数同型とし、既存根添加環の
自由性・忠実平坦性を移す。
続くBS専用予定`DeltaDivisionFiniteNormalizedBaseFlat.lean`で、その射と
零段から第N段への標準塔射を合成し、A/(p,d,a_s)から全有限段への
実際の係数射・標準係数の商像図式を構成する。
既存忠実平坦性の合成により、この適切な共通係数商上の全有限段の
忠実平坦性を証明する。全段極限と実完備化/perfectionへの接続、G4、
引用なし一般B4は引き続き未実装。

## B4-6：適切な係数商上の初期有限商の自由性・忠実平坦性（2026-10-15）

`DeltaDivisionFiniteNormalizedInitialFlat.lean`で、A/(p,d,a_s)から初期有限商への
具体的環射と代数構造を構成した。環射が元の基底係数の標準商像に一致する
図式を証明し、既存根添加表示をこの係数射に関する代数同型へ整えた。
既存根添加環の自由性・平坦性・零係数商も含む忠実平坦性を移した。
適切な係数商と具体的な標準係数射に関する公開定理であり、
元のA上の平坦性を仮定・主張していない。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
7公開宣言の対象3249ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。初期有限商比較は6c49ff6で個別コミット済み。
予定済みDeltaDivisionFiniteNormalizedBaseFlat.leanで、標準塔射と合成して
A/(p,d,a_s)上の全有限段の忠実平坦性へ進む。
G4、全段極限の平坦性、実完備化/perfectionの完全忠実平坦性と
引用なし一般B4は未実装。

## B4-6：適切な共通係数商上の全有限段の忠実平坦性（2026-10-15）

`DeltaDivisionFiniteNormalizedBaseFlat.lean`で、初期係数射と零段から第N段への
標準塔射を合成し、A/(p,d,a_s)から全有限正規化商への具体的係数射を
構成した。元の基底係数の標準商像に一致すること、任意の有限段間の
標準射に係数射が両立することを証明した。この射による代数構造を置き、
初期段と塔射の忠実平坦性を既存の合成定理でつないで全有限段の
忠実平坦性・平坦性と基底係数射の単射性を証明した。
全て正しい共通係数商上の具体的な環・射に関する公開定理。
零係数商を含み、p正則性・ghost射単射・u=δd・添字有限性・Noether性・
完備性は不要。7公開宣言の対象3250ジョブ、pure B4監査、全体4699ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
初期段の自由性・忠実平坦性は2617d9aで個別コミット済み。
全有限段の忠実平坦性が完成したが、全段極限・完備化/perfectionと
任意perfectoid商への適用は未完成であり、一般B4完成とは数えない。

次のBS専用予定`DeltaDivisionFiniteNormalizedDirectLimit.lean`で、
今回の標準塔射のDirectedSystem実体と、Mathlibの有向環直極限を用いた
具体的全段環を構成する。各段の標準射、射の互換性、各段射の単射性、
任意元の有限段表示、適切な共通係数商からの射と係数の標準像図式を証明する。
その後、実際の全δ関係イデアルの商とこの全段環の具体的比較へ進む。

### 共通基盤への要求 G5：平坦加群の自然数直系の直極限（未送信）

対象と正確な仮定・結論：可換環R、自然数で添字付けたR加群M_n、
線形遷移射f_ij : M_i →ₗ[R] M_j（i≤j）とDirectedSystem条件、
全nのModule.Flat R M_nから
Module.Flat R (Module.DirectLimit M f)を結論する公開定理。
有限生成性・有限表示性・Noether性・遷移射の単射性は仮定しない。
利用工程：B4-6のmod(p,d)除算δ環の全段平坦性。
既存APIで足りない点：Mathlibと共有コードを調査した範囲ではこの公開定理は
見つからない。既存TensorProduct.directLimitLeft/Rightと有限段平坦性、
既存直極限の零条件比較を再利用できるが、一般平坦性の接続は未公開。
待つ工程：加群直極限との具体的同型を用いて全段環の平坦性を結論する部分。
独立に進める作業：BS固有の標準環直系・全段環と係数射、実際の
全δ剰余商との同型、有限段・全段での通常射図式と普遍性。
この要求を理由に独立したBS構成を停止せず、新しい仮定定理や引用も追加しない。
G4、実完備化/perfectionの完全忠実平坦性と引用なし一般B4も未実装。

## B4-6：標準有限商からの具体的全段環と単射性（2026-10-15）

`DeltaDivisionFiniteNormalizedDirectLimit.lean`で標準有限商射のDirectedSystem
実体を置き、Mathlibの有向環直極限を用いた具体的全段環を構成した。
各有限段からの標準環射と互換性、各段射の単射性、全段環の任意元の
具体的有限段表示を証明した。適切な共通係数商A/(p,d,a_s)からの射も
構成し、任意有限段の係数射との合成に一致すること、元の基底係数の
標準商像の図式と全段係数射の単射性を証明した。
一般直極限の型・構造を重複構築せず、有限段の通常射を再利用した。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
10公開宣言の対象3251ジョブ、pure B4監査、全体4699ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
共通係数商上の全有限段の忠実平坦性は71ac240で個別コミット済み。
全段環の構成・単射性は証明済みだが、全段平坦性はまだ証明していない。

次のBS専用予定`DeltaDivisionFiniteNormalizedDirectLimitAlgebra.lean`で、
全段係数射による適切な共通係数商上の代数構造を置き、有限段の標準
塔射と全段への標準射をその共通係数商上の具体的代数射へ整える。
共通基盤G5の加群直極限との比較に使う実際の線形射の系も構成する。
さらにBS専用予定`DeltaDivisionNormalizedDirectLimitEvaluation.lean`で、
無限相対自由多項式環から全段環への具体的射を作る。
各変数の像は、その変数を含む有限段の標準商像で定義し、
任意の後段の同じ変数の像に一致することを互換性から証明する。
有限初期多項式環の包含と各段の標準商射の可換図式を供給し、
全段環への射の全射性、実際の全関係イデアルとの比較へ進む。
G5を待つ工程は一般平坦性の適用のみとし、この具体的BS構成を進める。
G4、実完備化/perfectionの完全忠実平坦性と引用なし一般B4は未実装。

## B4-6：全段環と有限商直系の共通係数商上の代数射・線形射（2026-10-15）

`DeltaDivisionFiniteNormalizedDirectLimitAlgebra.lean`で、全段係数射による
A/(p,d,a_s)上の代数構造を置き、各有限段間の標準射と各段から全段への
標準射をこの共通係数商上の代数射・線形射へ整えた。
共通係数射との可換性は既存の実際の環射の合成式を再利用し、線形射の
直系条件も環直系と同じものであることを証明した。
G5の加群直極限との比較で使う具体的射の型が確定した。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
6公開宣言の対象3252ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。全段環と標準射はf7f1d08で個別コミット済み。
予定済みDeltaDivisionNormalizedDirectLimitEvaluation.leanで、無限自由環の
基底係数と変数の具体的評価、有限段図式、全射性を証明する。
G5、G4、実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

## B4-6：無限相対自由環から全段環への具体的評価射と全射性（2026-10-15）

`DeltaDivisionNormalizedDirectLimitEvaluation.lean`で、各自由変数の像を
その変数を含む最初の有限段の標準商像として構成し、任意後段での像と
一致することを証明した。基底係数射とこの変数像による具体的評価射を
定義し、係数・変数上の式、任意有限初期多項式環への制限の可換図式を
証明した。全段環の任意元を有限段の商多項式で表すことで評価射の全射性も
証明した。これは正規化した通常全段環への全射性であり、一般B4の
perfectoid化射の全射性とは区別する。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
8公開宣言の対象3253ジョブ、pure B4監査、全体4699ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
共通係数商上の代数・線形射は1af8dbcで個別コミット済み。

次のBS専用予定`DeltaDivisionNormalizedDirectLimitKernel.lean`で、
評価射の有限初期環への制限の零条件がその段の具体的有限イデアル所属と
同値であることを各段射の単射性から証明する。
無限相対自由環の任意多項式の有限初期環による表示を既存rename APIから
構成し、評価射の核が各有限イデアルの包含mapのiSupに一致することを
証明する。これにより具体的全段正規化商と全段環の商同型へ進む。
G5、G4、実完備化/perfectionの完全忠実平坦性と引用なし一般B4は未実装。

## B4-6：具体的全段評価射の核と全段正規化商の環同型（2026-10-15）

`DeltaDivisionNormalizedDirectLimitKernel.lean`で、無限相対自由環の任意多項式が
有限初期変数の標準包含像であることを、有限変数の最大段と既存rename APIから
証明した。有限初期多項式の評価の零条件が、その段の具体的表示イデアルへの
所属と同値であることを各段射の単射性から証明し、核のcomapも同定した。
各有限表示イデアルの包含mapのiSupとして全段正規化イデアルを定義し、
評価射の核がその具体的イデアルに一致することを証明した。
既存商第一同型定理で全段正規化商と構成済み全段環の具体的環同型を構成し、
元の標準商射と評価射の図式、基底係数の全段係数射の図式も証明した。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
8公開宣言の対象3254ジョブ、pure B4監査、全体4711ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
全段評価射と全射性はb47396eで個別コミット済み。

次のBS専用予定`DeltaDivisionInfiniteWittNormalization.lean`で、
(p,Cd)を加えた実際のδ閉包が深さN+1有限関係イデアルの同じ剰余イデアルを
加えたもののiSupであることを、既存δ閉包・有限深さの単調性から証明する。
既存全有限段の逆Witt座標map式とIdeal.map_iSupを使い、その実際の全段
イデアルの逆座標像が今回の具体的全段正規化イデアルと一致することを
証明する。基底・自由環p乗算単射、自由環ghost単射、u=δdは明示仮定に維持する。
このmap式から実際のmod(p,d)全δ剰余商と全段環の具体的環同型を構成し、
標準商射と基底係数の図式を証明する。有限・全段関係イデアルを再定義しない。
G4、G5、実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

## B4-6：実際のraw δ閉包の全段Witt正規化とmod(p,d)商の比較（2026-10-15）

`DeltaDivisionInfiniteWittNormalization.lean`で、(p,Cd)を加えた実際のraw δ閉包が
深さN+1の有限剰余イデアルの上限であることを既存δ閉包の表示と有限段の
単調性から証明した。既存の全有限段逆座標map式とIdeal.map_iSupにより、
この実際の全段イデアルの逆Witt座標像が具体的全段正規化イデアルと一致する
ことを証明した。実際のmod(p,d)全δ剰余商と構成済み全段環の具体的環同型を
構成し、標準商射上の逆座標評価図式、基底係数の全段係数射図式も証明した。
raw δ閉包、有限関係イデアルを再定義せず、全段正規化商同型を再利用した。
cofinal上限式には正則性等は不要。Witt比較と商同型には基底・自由環の
p乗算単射、自由環ghost射単射、指定単元u=δdを明示仮定として維持した。
5公開宣言の対象3255ジョブ、pure B4監査、全体4712ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
全段核同定と正規化商同型は2400159で個別コミット済み。
これはDeltaAdjoinDivisionのraw δ閉包による商のmod(p,d)比較であり、
DeltaDivisionTorsionQuotientや古典的・導来完備化の平坦性はまだ供給しない。
元の一般perfectoid化射の全射性・André引用解消もまだ未達。

次のBS専用予定`DeltaDivisionInfiniteWittNormalizationAlgebra.lean`で、
この実際のraw mod(p,d)商へのA/(p,d,a_s)からの具体的係数射を構成する。
標準係数の商像との図式を証明し、今回の環同型を共通係数商上の代数同型へ
整える。G5の結果を移せる具体的構造として供給する。
またBS専用予定`DeltaDivisionNormalizedDirectLimitModule.lean`で、
構成済み全段環を、既存の共通係数商上の具体的線形塔射による
Module.DirectLimitと比較する。Mathlibの普遍性を再利用した線形同型を構成し、
各段の標準線形射上の図式を証明する。G5待ちはその比較を使った平坦性の
適用のみとし、具体的比較とraw全δ商の表示は独立に進める。
その後、dねじれ除去・古典的／導来完備化・perfectionとの正確な比較へ進む。
G4・G5への接続、実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

## B4-6：実際のraw全δ剰余商の共通係数商上の代数表示（2026-10-15）

`DeltaDivisionInfiniteWittNormalizationAlgebra.lean`で、適切な共通係数商
A/(p,d,a_s)から実際のraw mod(p,d)全δ商への具体的係数射を構成した。
元の基底係数の標準商像との一致を証明し、この射による代数構造を置いた。
実際の全δ商と全段環の比較を、この標準共通係数射に関する代数同型へ
整えた。全段係数射の単射性から実際の全δ商への係数射の単射性も証明した。
基底・自由環のp乗算単射、自由環ghost射単射、指定単元u=δdは明示仮定。
5公開宣言の対象3256ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。実際のraw全δ商の環比較はfd6b532でコミット済み。
直前の全体ビルドは共有側変更に伴い4712ジョブだった。
全段平坦性やdねじれ除去、古典的／導来完備化、perfectionの平坦性は
まだ証明していない。一般B4とAndré引用の解消は未完成。

予定済みDeltaDivisionNormalizedDirectLimitModule.leanで、共通係数商上の
具体的線形塔射によるModule.DirectLimitと構成済み全段環の線形同型を
Mathlibの普遍性から構成する。G5の適用先を具体化し、実際の全δ商への
移送は今回の代数同型で行う。G5を待たずに比較と各段の標準射図式を進める。
G4への接続、実完備化/perfectionの完全忠実平坦性と一般B4も引き続き未実装。

## B4-6：構成済み全段環と具体的加群直極限の線形同型（2026-10-15）

`DeltaDivisionNormalizedDirectLimitModule.lean`で、既存の共通係数商上の
標準線形塔射によるModule.DirectLimitを使い、各段の標準線形射を
その普遍性で全段環へまとめた具体的線形射を構成した。
各段の標準像の図式を証明し、有限段表示と各段射の単射性からこの射の
全単射性を証明して、加群直極限と構成済み全段環の線形同型を構成した。
同型自身の各段上の図式も供給した。加群直極限一般論を重複構築していない。
p正則性・ghost射単射・u=δd・添字有限性・Noether性・完備性は不要。
5公開宣言の対象3257ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。実際のraw全δ商の代数表示はa0f396dでコミット済み。

次のBS専用予定`DeltaDivisionNormalizedDirectLimitFlat.lean`では、
既存TensorProduct.directLimitLeftとModule.DirectLimit.of.zero_exactを使い、
この具体的BS線形塔についてテンソルが単射を保存することを直接証明する。
一般平坦直極限定理の新規構築はせず、公開定理の対象をBSの具体的加群
直極限・全段環に限定する。有限段平坦性と既存の直系・零判定APIを再利用する。
この特殊化の経路が成立すれば、G5の一般要求とは分けてBSの全段平坦性を
接続済みとし、raw全δ商への移送も既存代数同型で行う。
現時点で全段平坦性はまだ未実装。G4、実完備化/perfectionの
完全忠実平坦性と一般B4も未完成。

## B4-6：具体的全段環とraw全δ剰余商の平坦性（2026-10-15）

`DeltaDivisionNormalizedDirectLimitFlat.lean`で、BSの具体的加群直系について
テンソルが単射を保存することを直接証明した。既存テンソルと直極限の
比較、直極限の零判定、有限段平坦性を使い、テンソルで作る各段の射の
可換性と誘導直極限射の単射性を示した。一般平坦直極限定理は新設していない。
具体的加群直極限の平坦性を構成済み全段環へ線形同型で移し、
実際のraw mod(p,d)全δ剰余商へ既存代数同型で移した。
全段環の平坦性にはp正則性・ghost射単射・u=δdは不要。
実際のraw全δ商への移送には既存Witt比較の明示仮定を維持した。
3公開定理の対象3258ジョブ、pure B4監査、全体4720ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
加群直極限比較は30aac64で個別コミット済み。
G5の一般補題は未公開だが、このBS工程の平坦性は特殊化により接続済みで
G5待ちではなくなった。共通一般補題の重複は作っていない。
全段の忠実平坦性、dねじれ除去、導来完備化/perfectionへの接続と一般B4は未完成。

次のBS専用予定`DeltaDivisionNormalizedTensorTransition.lean`で、
任意の共通係数商加群Nに対して有限段間の標準線形射をrTensor Nした射が
単射であることを、有限段間の忠実平坦性と既存の係数塔のテンソル結合則で
証明する。一般純射の新規定理は作らず、この具体的有限商直系に限定する。
続くBS専用予定`DeltaDivisionNormalizedDirectLimitFaithfullyFlat.lean`では、
各段テンソル射の単射性と既存直極限の零判定により、テンソル直極限への
各段射の単射性を証明する。初期有限段の忠実平坦性と直極限のテンソル比較で
全段環のテンソルが零加群を反映することを示し、全段忠実平坦性へ進む。
その後、raw全δ商への移送とdねじれ除去・実完備化/perfectionとの正確な比較へ進む。
G4、実完備化/perfectionの完全忠実平坦性と引用なし一般B4は引き続き未実装。

## B4-6：有限商の標準射の任意テンソル後の単射性（2026-10-15）

`DeltaDivisionNormalizedTensorTransition.lean`で、任意n≤mの標準有限商線形射を
共通係数商上の任意加群NとrTensorした射が単射であることを証明した。
有限段間の忠実平坦性、標準共通係数射による係数塔、既存テンソルの
異なる基底環に関する結合則と右単位同型を用いた。
既存の忠実平坦代数への標準テンソル射の単射性を移し、移した射が実際の
標準有限商射のrTensorと一致することを具体的図式で確認した。
一般純射の定理を新設せず、BSの具体的直系に限定した公開定理。
任意宇宙の加群、零係数商、任意添字族を扱い、正則性・Noether性・完備性は不要。
1公開定理の対象3259ジョブ、pure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。全段平坦性は5a51bf9で個別コミット済み。
予定済みDeltaDivisionNormalizedDirectLimitFaithfullyFlat.leanで、
この単射性をテンソル直極限の各段射に移し、全段の忠実平坦性へ進む。
G4、dねじれ除去、実完備化/perfectionの完全忠実平坦性と一般B4は未実装。

## B4-6：全段環とraw全δ商の忠実平坦性（2026-10-15）

`DeltaDivisionNormalizedDirectLimitFaithfullyFlat.lean`で、任意の共通係数商加群と
テンソルした具体的直極限への各段の標準射が単射であることを、既存の
直極限の零判定と有限段間テンソル単射性から証明した。
初期有限段の忠実平坦性、テンソルと直極限の比較、構成済みの加群直極限
線形同型を合成して、全段環とのテンソルが零加群を反映することを証明した。
全段平坦性と合わせ、標準係数射によるA/(p,d,a_s)上の全段環の
忠実平坦性を証明した。既存代数同型により実際のraw mod(p,d)全δ商へも移した。
一般忠実平坦直極限定理は新設せず、BSの具体的対象・標準写像に限定した。
零係数商・任意添字族を含む。全段環には正則性・ghost単射・u=δdは不要。
raw全δ商への移送には既存Witt比較の明示仮定を維持した。
3公開定理の対象3260ジョブ、pure B4監査、全体4722ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
有限段テンソル単射性はc89a62eで個別コミット済み。
G5の一般要求を待たず、このBS工程の全段忠実平坦性まで接続済みとなった。
これは適切な係数商上のraw mod(p,d)段階の結論であり、元のprism上の
完全忠実平坦性、dねじれ除去後・完備化・perfectionの性質はまだ供給しない。
一般B4・André引用の解消は引き続き未達。

次のBS専用予定`DeltaAdjoinDivisionResiduePresentation.lean`で、
既存DeltaAdjoinDivisionにおける(p,基底dの像)の通常イデアルを明示し、
その商を今回の無限自由環のsup-イデアルによる商へ二重商同型で接続する。
二段階のDeltaDivisionTorsionQuotientのadic idealと区別し、raw段階の
既存環・係数射を使った具体的比較にする。共通係数商からの射の標準像図式、
全段環への同型、今回の忠実平坦性の移送を供給する。
その後、選ぶ根添加族の相対正則性とTor条件、dねじれ除去・古典的／導来
完備化・perfectionとの正確な比較を進める。raw段階の忠実平坦性だけから
後続の完全忠実平坦性を推測せず、各比較・必要な条件を証明する。
G4への接続、実完備化/perfectionの完全忠実平坦性と引用なし一般B4は未実装。

## B4-6：既存DeltaAdjoinDivisionのraw (p,d)商の二重商表示（2026-10-15）

`DeltaAdjoinDivisionResiduePresentation.lean`で既存DeltaAdjoinDivision内の
(p,基底dの像)の通常イデアルとその商のabbrevを構成した。
イデアルが無限自由環の(p,Cd)の標準商射によるmapに一致することを証明し、
Mathlibの二重商同型を再利用して、既存添加環のraw (p,d)商と無限自由環の
(p,Cd)およびδ閉包のsupによる商との具体的環同型を構成した。
元の無限自由環の標準商像と、基底係数の標準商像の可換図式も証明した。
DeltaDivisionTorsionQuotientのadic idealを重複定義せず、raw段階を区別した。
p正則性・ghost射単射・単元条件・完備性は不要。
6公開宣言の対象3261ジョブとpure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。無限段の忠実平坦性は11faafbで個別コミット済み。

次のBS専用予定`DeltaAdjoinDivisionResidueFlat.lean`で、二重商同型と既存の
全段環同型を合成し、既存添加環のraw (p,d)商の全段表示を構成する。
適切な共通係数商からの具体的標準係数射と代数構造、標準係数上の図式を
供給し、全段環への代数同型で忠実平坦性・平坦性を移す。
原典Prop 3.13 pp.33–35を再確認した。相対完全正則性と導来完備pushoutが
必要であり、今回の通常商の忠実平坦性だけで原典の導来結論を置き換えない。
その後、根添加族について必要な相対正則性・Tor条件と
ねじれ除去・古典的／導来完備化・perfectionの比較へ進む。
G4への接続と一般B4・André引用の解消は未完成。

## B4-6：既存DeltaAdjoinDivisionのraw残余商の標準係数射と忠実平坦性（2026-10-15）

`DeltaAdjoinDivisionResidueFlat.lean`で、二重商表示と既存全段表示を合成し、
既存DeltaAdjoinDivisionのraw (p,d)商と全段環の具体的環同型を構成した。
元の基底係数の標準商像が全段係数射に一致する図式を証明し、適切な
共通係数商からの係数射と代数構造を置いた。この係数射が既存
 deltaAdjoinDivisionMapの標準残余商像であることも証明した。
全段表示を標準係数射についての代数同型へ整え、忠実平坦性・平坦性を
移した。基底・自由環p乗算単射、自由環ghost単射、u=δdは明示仮定。
8公開宣言の対象3262ジョブ、pure B4監査、全体4740ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
raw残余商の二重商表示は8ff81eaで個別コミット済み。
この結論はraw段階であり、ねじれ除去後や導来完備化の結論は未実装。

次のBS専用予定`DeltaRootRelationCoefficientQuotient.lean`で、任意元族b_s∈Aに
対し、既存rank-one多項式δ環A[X_s]に置く根関係X_s^p-C(b_s)を具体化する。
(p,Cd,根関係)による係数商が、既存MonicPowerFamilyCoverによる
A/(p,d)上の根添加環と同型であることを構成し、係数と根上の図式を証明する。
既存deltaDivisionFirstBaseIdeal・モニック根添加APIを再利用する。
その後、源多項式δ環のdistinguished生成元の単元条件、原典に必要な
相対正則性・Tor条件、実際のδ除算包への根の写像を進める。
G4、ねじれ除去・導来完備化/perfectionと一般B4は未実装。

## B4-6：根関係を入れた具体的係数商と根添加環の比較（2026-10-15）

`DeltaRootRelationCoefficientQuotient.lean`で、既存rank-one多項式δ環に置く
根関係族X_s^p-C(b_s)を具体的に定義した。既存deltaDivisionFirstBaseIdealを
使ってA[X_s]/(p,Cd,X_s^p-Cb_s)の係数商を置き、そのイデアルが
(p,d)の係数拡張と既存モニック根関係イデアルの和に一致することを証明した。
既存係数商・モニック根添加比較を合成し、A/(p,d)上の通常根添加環との
環同型、標準係数像と指定根像の図式を証明した。
6公開宣言の対象3264ジョブとpure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。既存raw残余商の忠実平坦性はce93010でコミット済み。
直前の全体ビルドは共有側変更に伴い4740ジョブだった。

次のBS専用予定`DeltaRootRelationCoefficientFlat.lean`で、A/(p,d)から
この具体的係数商への標準射・代数構造、根添加表示の代数同型、
自由性・忠実平坦性を供給する。さらに既存rank-one δ環における
基底dの像のdistinguished単元条件を用い、根関係を入れた実際のδ除算包に
今回のraw残余商の忠実平坦性を適用する準備を進める。
原典Definition 2.42 p.26も再確認した。相対完全正則性はKoszul複体間の
導来平坦性の条件であり、通常の係数商の平坦性だけでは完了と数えない。
既存Koszul・正則列・DerivedTensor APIを再利用して必要な比較を証明する。
G4、ねじれ除去・導来完備化/perfectionと一般B4は未実装。

## B4-6：根関係の係数商の標準射・自由性・忠実平坦性（2026-10-15）

`DeltaRootRelationCoefficientFlat.lean`でA/(p,d)から具体的な根関係の係数商への
標準係数射と代数構造を置き、その射が元の基底係数の標準商像に一致する
ことを証明した。根添加表示をこの係数射に関する代数同型へ整え、
既存モニック根添加環の自由性・忠実平坦性・平坦性を移した。
係数商の各変数のp乗が指定元の標準像に一致する具体的根の式も証明した。
零係数商・任意添字族を含む。正則性・ghost単射・完備性は不要。
8公開宣言の対象3265ジョブ、pure B4監査、全体4750ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
係数商の根添加表示はe97cfe5で個別コミット済み。
この通常の根添加係数商の結論を原典の導来正則性の代わりには使っていない。

次のBS専用予定`DeltaRootAdjoinDivisionResidue.lean`で、既存rank-one多項式δ環を
源とし、Cdで根関係X_s^p-C(b_s)をδ除算する実際のraw添加環と残余商を
具体化する。Cdのδ値の単元条件を既存係数δ射の自然性で供給し、
共通係数商A/(p,d)から残余商への標準射・標準像図式を構成する。
今回の係数商の忠実平坦性と既存raw残余商の忠実平坦性を合成し、
その射の忠実平坦性と残余商の具体的p乗根を供給する。
root用のδ環・p乗算単射・ghost単射の必要箇所を明示して既存APIを再利用する。
続いて、有限根関係族の相対正則性と既存Koszul/DerivedTensorによる比較、
実際の完備化/perfectionへ進む。一般B4とAndré引用の解消は未完成。

## B4-6：根添加を入れた実際のrawδ除算残余商（2026-10-15）

`DeltaRootAdjoinDivisionResidue.lean`で、既存rank-one多項式δ環を源とし、
Cdで根関係X_s^p-C(b_s)をδ除算する既存添加環のraw残余商を具体化した。
源のCdのδ値が基底の指定単元の係数像に一致することを証明し、
A/(p,d)から残余商への標準係数射と代数構造、元の係数像の図式を構成した。
根関係の係数商の忠実平坦性と既存raw残余商の忠実平坦性を合成し、
この標準射の忠実平坦性・平坦性を証明した。源変数の標準商像が指定元の
p乗根となることも、具体的環・写像について証明した。
源多項式環と相対自由環のp乗算単射・相対自由環ghost単射、u=δdは明示仮定。
9公開宣言の対象3266ジョブ、pure B4監査、全体4750ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
根関係の係数商の忠実平坦性は111f660で個別コミット済み。
これはraw mod(p,d)残余段階の結論であり、まだperfectoidな忠実平坦拡大ではない。

次のBS専用予定`DeltaRootAdjoinDivisionVariables.lean`で、raw添加環内の
源多項式変数の像を具体化する。この元のδ値が零であること、p乗と指定元の
係数像の差がdの像と除算変数の積であることを、既存δ係数射・除算関係から
証明する。任意の通常環射でdの像を消せば実際のp乗根になる図式も供給する。
続いて既存完全δ環の逆Frobeniusを使い互換p冪根列へ進む。
根のperfectoid候補とその標準射のCFFは区別し、相対正則性・Tor条件と
導来完備化/perfectionの比較を証明する。一般B4・André引用解消は未完成。

## B4-6：raw根添加環のrank-one変数と実際の根関係（2026-10-15）

`DeltaRootAdjoinDivisionVariables.lean`で既存rank-one多項式δ環の根関係を
Cdでδ除算したraw添加環と、その源変数の標準δ係数像を具体化した。
この元のδ値が零であることを既存δ係数射と源変数のδ値零から証明した。
そのp乗と指定元の係数像の差がdの像と除算変数の積である実際の環内の
等式を証明し、dの像を消す任意通常環射の先では実際のp乗根になる図式を
供給した。残余商自体にδ構造は仮定していない。
p正則性・ghost単射・単元条件・完備性は不要。
5公開宣言の対象3267ジョブとpure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。根δ除算残余商の忠実平坦性はb8e3216でコミット済み。

次のBS専用予定`PerfectDeltaRankOneRoots.lean`で、既存完全δ環の逆Frobeniusを
反復し、δ値零の指定元に対する具体的互換p冪根列を構成する。
各段のδ値零、次段のp乗が前段に一致する式、通常環射での像の互換性を
証明する。既存の互換根列の条件を用い、新たな同等の根列述語は定義しない。
続いてraw根添加環から完備化/perfectionへの既存δ射を使い、この列を
実際のperfectoid候補の商での根列へ移す。CFFの証明とは明確に分ける。
相対正則性・Torと実完備化/perfectionの比較、一般B4は未完成。

## B4-6：完全δ環のrank-one元の具体的互換根列（2026-10-15）

`PerfectDeltaRankOneRoots.lean`で、既存Frobenius環同型の逆を反復した
指定元の根列を構成した。零段・後続式、δ値零の元なら各段もδ値零であることを
既存の逆Frobeniusのδ射性から証明した。次段のp乗が前段に一致する互換式、
任意通常環射による根列の像の互換式も証明した。
δ環固有の構成であり、同等の互換根列述語やperfectoid化の定義は新設していない。
必要な仮定は完全δ性と指定元のδ値零のみ。完備性はこの根列構成には不要。
6公開宣言の対象3271ジョブとpure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。raw変数のrank-one性と根関係はada5436でコミット済み。

次のBS専用予定`DeltaRootAdjoinCompatibleRoots.lean`で、raw根添加環から
任意の完全δ環へのδ射と、その先のdの像を消す通常環射を指定し、
指定元の像を零段とする具体的互換p冪根族を構成する。
raw根変数のδ値零と根関係を使い、最初の根のp乗と零段の像の一致を証明する。
この射を既存完備化/perfection・完全prism候補へ適用する工程と、
標準射の完全忠実平坦性を証明する工程は区別する。
一般B4、相対正則性・Torと完備化/perfectionのCFFは未完成。

## B4-6：根δ除算包から完全δ環の通常商への互換根族（2026-10-15）

`DeltaRootAdjoinCompatibleRoots.lean`で、raw根添加環から指定した完全δ環への
δ射と、その先の通常環射を入力とする具体的根族を構成した。
零段を指定元の係数像とし、以降をraw根変数の像への逆Frobenius列の像とした。
raw根変数のδ値零がδ射で保存されること、零段・後続段の具体式を証明した。
dの像が通常環射で零となる仮定の下、最初の根のp乗は零段に一致し、
以降も全段で互換p冪根条件を満たすことを証明した。
商にδ構造は仮定せず、根列の同等の述語も新設していない。
5公開宣言の対象3272ジョブ、pure B4監査、全体4750ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
完全δ環の具体的根列はcda9c6aで個別コミット済み。
これは実際の根列の構成であり、標準射の完全忠実平坦性はまだ結論していない。

次のBS専用予定`DeltaRootPerfectoidCandidate.lean`で、既存PCompletedDeltaDivision、
perfectDeltaPDPrismおよびそのperfectoid商APIを用いて、根族を持つ具体的
perfectoid候補と基底射を構成する。源rank-one多項式δ環のCdのdistinguished性、
各標準δ射との図式を供給し、今回の根族をその商に適用する。
既存の完備化・prism・IsIntegralPerfectoidを再利用し、一般定義は重複しない。
候補のperfectoid性・根列の存在と、基底射のCFFは分けて報告する。
CFFに必要な相対正則性・Koszul/DerivedTensorの比較と完備化/perfectionの
性質を証明する工程、一般B4・André引用解消は未完成。

## B4-6：根族を持つ具体的perfectoid候補と基底射（2026-10-15）

`DeltaRootPerfectoidCandidate.lean`で、既存のp進完備δ除算完全化と
実導来(p,d)完備化H⁰を合成した具体的完全prism候補を構成した。
基底δ環Aのdistinguished元dと族b:σ→Aのみを入力とし、rank-one多項式
δ環・raw根δ除算包からの既存標準δ射を使用した。
その通常商の整perfectoid性、A/(d)からの具体的基底射と商代表の図式、
指定元b_sの基底像から始まる互換p冪根族を証明した。
候補の商のp正則性・非零性・源δ環の完全性は要求しない。
既存の実導来完備化と完全prismの商の定理を使用し、導来完備化を
条件なしに古典的完備化へ置き換えてはいない。
17公開宣言の対象3762ジョブ、pure B4監査、全体4757ジョブ成功。
全体は共有側の既存警告を含む。標準3公理のみ、新sorry・公理・引用なし。
前段の抽象互換根族はcc22894で個別コミット済み。

**未完成の境界**：この候補の標準射が完全忠実平坦とはまだ証明していない。
raw残余商の通常忠実平坦性から完備化/perfection後のCFFは自動ではない。
従って根族付き完全忠実平坦perfectoid拡大の存在・一般B4・André引用解消は未完成。

次のBS専用予定`DeltaRootRelationKoszul.lean`で、有限個の源根関係
X_s^p-C(b_s)の弱正則性・Koszul分解を、既存の通常冪根添加環の
自由性・モニック性と共通KoszulResolution APIで証明する。
任意基底変更後でも根関係が正則であることと、係数側のKoszul複体を
伴う相対的な比較を区別する。源(p,d)の正則性は無条件に追加しない。
続いてδ関係の有限段、既存実DerivedTensor/導来完備化の比較を扱い、
mod(p,d)の通常商の忠実平坦性だけで原典の相対完全正則性やCFFを
結論しない。一般B4の公開全射性定理へはCFFを実証してから接続する。

## B4-6：単独根関係の普遍正則性と実Koszul分解（2026-10-15）

`DeltaRootRelationKoszul.lean`で、任意係数環A・添字σ・族bに対し、
各根関係X_s^p-C(b_s)の乗法単射を証明した。
指定変数をOption添字分解で一変数多項式として取り出し、
モニック多項式の正則性を使用した。単独の根関係の弱正則性から
既存共通KoszulResolution APIで実際の通常商のKoszul分解を証明した。
任意の係数環射A→Bによる根関係の標準像にも同じ正則性・Koszul分解を供給した。
係数環のp正則性・非零性・Noether性は不要。零環・pねじれも許す。
5公開定理の対象3512ジョブ、pure B4監査、全体4757ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
根族付き具体的perfectoid候補はf29b726で個別コミット済み。

これは単独根関係についての実分解であり、有限列全体や相対完全正則性の
完成とは数えない。候補標準射のCFF・一般B4はまだ未完成。
次のBS専用予定`DeltaRootPartialQuotient.lean`で、先行する添字集合の
根関係で割った多項式環を、既存MonicPowerFamilyCoverを係数環として
残りの変数を持つ多項式環と同定する。添字分割と標準係数・変数の図式を
明示し、重複する一般根添加環の定義は作らない。
これにより異なる有限個の根関係を順に課した商で後続根関係が
非零因子となることを今回の定理から導き、既存弱正則列/Koszul分解へ接続する。
源の(p,d)の正則性は無条件に仮定せず、係数側Koszul複体を伴う相対比較、
δ関係の有限段および実導来完備化/perfectionのCFFは後続工程として残す。

## B4-6：先行根関係の商表示と後続関係の正則性（2026-10-15）

`DeltaRootPartialQuotient.lean`で、添字τ⊕ιを残りの変数τと先行変数ιに
分割し、先行側の根関係のみで割るイデアルを具体化した。
MathlibのsumRingEquiv・係数商同型と既存根添加の商表示同型を合成し、
この商をMvPolynomial τ (MonicPowerFamilyCover p ι A b_inr)と同定した。
標準商射上の式、元の係数・残りの変数・先行指定根の図式を証明した。
商表示はpの素数性・正則性・非零性を不要とする。
pが素数なら、この商の各後続根関係が非零因子となることと、
その一関係の実Koszul分解を前工程から導いた。
先行添字ιの有限性も不要。候補のCFFをこれだけで結論していない。
9公開宣言の対象3513ジョブ、pure B4監査、全体4757ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
単独根関係の普遍正則性とKoszul分解は8e5ab1cで個別コミット済み。

次のBS専用予定`DeltaRootSubsetQuotient.lean`で、任意の先行添字集合T⊆σに
対し、補集合⊕Tへの再添字付けを今回の商表示へ接続する。
先行部分集合の根関係イデアル、商同型、Tに属さない根関係の像の
正則性を証明する。これを有限列の各prefixへ適用して、異なる有限個の
根関係の弱正則性・実Koszul分解を得る。
相対(p,d)Koszul比較とδ関係の有限段、実導来完備化/perfectionのCFF、
根族付き完全忠実平坦perfectoid拡大の存在、一般B4は未完成。

## B4-6：任意先行添字集合の商同型と後続根関係の正則性（2026-10-15）

`DeltaRootSubsetQuotient.lean`で、任意T⊆σに対する補集合⊕Tへの
具体的添字同型を供給し、T内・T外の添字の図式を証明した。
T内の根関係だけを課すイデアルが再添字付けで既存部分根関係
イデアルへ移ることを証明し、前工程の商表示を合成した。
結果はMvPolynomial (Tᶜ) (MonicPowerFamilyCover p T A (b|T))との環同型。
係数、T外の標準変数、T内の指定根の図式を明示した。
pが素数なら、T外の各根関係の標準商像が非零因子となることを証明した。
T・σの有限性、Aの非零性・p正則性・Noether性は不要。
既存根添加環を使用し、同等の一般環や一般述語は新設していない。
10公開宣言の対象3514ジョブ、pure B4監査、全体4762ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
直和添字による先行根関係の商表示はc0857f4で個別コミット済み。

次のBS専用予定`DeltaRootFiniteRegularSequence.lean`で、重複のない有限列
l:List σに対し、根関係の列l.map(deltaRootRelationFamily b)が弱正則で
あることを証明する。各先行部分の生成イデアルを今回のT部分集合
イデアルと同定し、後続添字がTに属さないことをList.Nodupから供給する。
既存共通KoszulResolution APIからFin nで指定する有限根関係の
実Koszul分解を導き、任意係数変更後にも適用する。
これは係数側(p,d)のKoszul複体を伴う相対比較と区別する。
δ関係の有限段、実導来完備化/perfectionのCFF、一般B4は未完成。

## B4-6：有限根関係列の普遍弱正則性と実Koszul分解（2026-10-15）

`DeltaRootFiniteRegularSequence.lean`で、有限添字列の根関係の生成イデアルを
その添字集合の根関係イデアルと同定した。重複のない列l:List σの各先行部分に
前工程の任意部分集合の商の正則性を適用し、根関係列全体の弱正則性を証明した。
Fin n→σの単射で指定する有限族へ移送し、共通KoszulResolution APIから
実際の通常商のKoszul分解を得た。任意係数環射A→Bによる根関係の標準像にも
同じ実Koszul分解を供給した。
Aのp正則性・非零性・Noether性は不要。n=0も含む。
5公開定理の対象3515ジョブ、pure B4監査、全体4762ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
任意部分集合の商同型・後続正則性は3b54c5cで個別コミット済み。

次のBS専用予定`DeltaRootSubsetFlat.lean`で、任意部分集合の根関係の商表示を
標準A代数同型へ強化し、既存根添加環上の多項式環の自由性・忠実平坦性を移送する。
今回のKoszul分解と合わせて、有限根関係の実商がA上平坦であることを明示する。
その後、係数側(p,d)のKoszul複体を伴う相対比較とδ関係の有限段へ進む。
根関係の通常の弱正則性だけで、実導来完備化/perfection後のCFFを結論しない。
根族付き完全忠実平坦perfectoid拡大の存在、一般B4は未完成。

## B4-6：任意部分根関係商の標準係数射に関する自由性・忠実平坦性（2026-10-15）

`DeltaRootSubsetFlat.lean`で、既存の任意部分集合の商表示を標準A代数同型に強化した。
既存MonicPowerFamilyCover上の多項式環の自由性・忠実平坦性をこの同型で移送し、
任意T⊆σの根関係の商が元の係数環A上自由・忠実平坦・平坦となることを証明した。
Tの有限性、Aの非零性・p正則性・Noether性は不要。
対象は未完備の通常商であり、源多項式環上の平坦性とは主張していない。
4公開宣言の対象3516ジョブ、pure B4監査、全体4762ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
有限根関係列の弱正則性と実Koszul分解はe25835eで工程別コミット済み。

次のBS専用予定`DeltaRootFiniteTor.lean`で、有限根関係の実商を標準A代数として
具体化し、今回の部分集合商の平坦性と既存Tor/DerivedTensor APIから、
任意A加群Nとの高次Tor消滅・実導来テンソルの次数零集中を供給する。
根関係の有限Koszul分解とこの係数側Tor計算を相対Koszul比較へ接続する。
同等のTorや完全平坦性の定義・一般補題は重複して作らない。
係数側(p,d)のKoszul複体が次数零とは仮定せず、相対比較と通常商の平坦性を区別する。
δ関係の有限段、実導来完備化/perfectionのCFF、一般B4・André引用解消は未完成。

## B4-6：有限根関係の実商の係数側Torと平坦係数拡大後のTor（2026-10-15）

`DeltaRootFiniteTor.lean`で、有限族s:Fin n→σの実根関係イデアルを
その添字像の部分集合イデアルと同定し、標準A係数射による実商の
平坦性・忠実平坦性を供給した。添字の単射性はこの平坦性には不要。
既存TorとDerivedTensorを使い、任意A加群Nとの高次Tor消滅と
実導来テンソルの次数零集中を証明した。
さらに共通TorFlatBaseChangeVanishingの平坦係数拡大定理を使用し、
B=MvPolynomial σ A上のTor_{>0}^B(B/(g), B⊗_A N)も零となること、
対応する実導来テンソルが次数零に集中することを証明した。
源B上の任意加群とのTorを零とは主張していない。Aのp正則性・非零性・
Noether性は不要。係数側(p,d)Koszul複体の次数零集中は仮定していない。
7公開定理の対象3565ジョブ、pure B4監査、全体4807ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
部分根関係商の自由性・忠実平坦性は7f53f95で工程別コミット済み。

次のBS専用予定`DeltaRootFiniteKoszulCoefficients.lean`で、有限根関係の
実Koszul分解と共通koszulModuleTorComparison、torModuleCommを用いて、
B⊗_A Nを係数とする根関係Koszul複体の負次数ホモロジー消滅を証明する。
任意A加群Nを許し、N=A/Iもそのまま適用できる形にする。
比較には共通のテンソル/反復錐の自然同型を使用し、同等のKoszul・Tor定義は作らない。
これを係数側(p,d)Koszul複体を伴う相対比較に接続する。
δ関係の有限段、実導来完備化/perfectionのCFF、一般B4は未完成。

## B4-6：任意係数加群での有限根関係Koszulホモロジーの実計算（2026-10-15）

`DeltaRootFiniteKoszulCoefficients.lean`で、単射s:Fin n→σで指定する根関係について、
任意A加群Nから得るB⊗_A Nを係数とした既存反復錐Koszul複体の
負次数ホモロジーを実商Q=B/(g)とのTor_B(Q,B⊗_A N)へ結ぶ線形同型を供給した。
共通koszulModuleTorComparisonの自然比較とtorModuleCommの合成を使用した。
前工程のTor消滅から全負次数のSubsingleton・IsZeroを証明し、
N=A/I（任意係数イデアルI）の場合も公開した。
零次数は既存Tor零次数同型とテンソルの係数拡大取消同型を合成し、
Q⊗_A Nとの具体的なB線形同型を供給した。
Nの平坦性・有限性、Aのp正則性・非零性・Noether性は不要。
係数側(p,d)Koszul複体そのものの次数零集中は仮定していない。
5公開宣言の対象3585ジョブ、pure B4監査、全体4807ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
有限根関係商と係数拡大加群のTor消滅は7bac439で工程別コミット済み。

次のBS専用予定`DeltaRootFiniteKoszulAugmentation.lean`で、今回の零次数同型と
共通KoszulModuleBounds・toSingleOfHomology APIを使い、根関係の
係数付きKoszul複体から(Q⊗_A N)[0]への具体的な擬同型を構成する。
正次数の零性も既存複体の支持範囲から供給し、任意非零次数の消滅を明示する。
続いて係数側の有限Koszul操作（特にp,d）との相対比較を行う。
同等の複体・Koszul・Tor定義は新設せず、既存比較・実写像を使用する。
δ関係の有限段、実導来完備化/perfectionのCFF、一般B4は未完成。

## B4-6：係数付き根関係Koszul複体の具体的な実商への擬同型（2026-10-15）

`DeltaRootFiniteKoszulAugmentation.lean`で、共通KoszulModuleBoundsによる
正次数の支持範囲と前工程の負次数消滅を合わせ、任意の非零整数次数で
係数付き根関係Koszul複体のホモロジーが零となることを証明した。
零次数から一次数への微分の零性と既存toSingleOfHomologyを使い、
この複体から実通常テンソル積(Q⊗_A N)[0]への具体的な鎖写像を構成した。
Qは標準有限根関係の実商であり、前工程の零次ホモロジー同型を使用した。
この写像の擬同型性と、零次ホモロジー射がその具体的同型に一致する図式を証明した。
任意A加群Nを許し、Nの平坦性・有限性、Aのp正則性・非零性・Noether性は不要。
5公開宣言の対象3587ジョブ、pure B4監査、全体4808ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
係数付きKoszulホモロジーの実計算はcf4d2adで工程別コミット済み。

次のBS専用予定`DeltaRootRelativeKoszul.lean`で、今回の具体的添加写像に
係数側の任意有限列a:Fin m→AのKoszul操作を施す。
標準係数像C(a_i)の反復錐を使った実写像
K(Ca;K(g;B⊗_A N))→K(Ca;(Q⊗_A N)[0])を供給し、
共通scalarConeFunctor_map_quasiIsoと有限帰納法から擬同型性を証明する。
特にa=(p,d)へ適用し、係数側のKoszul複体を次数零と仮定しない相対比較を得る。
同等の一般Koszul保存定理・定義は新設せず、この具体的写像への適用を供給する。
δ関係の有限段、実導来完備化/perfectionのCFF、一般B4は未完成。

## B4-6：係数側有限Koszul操作を伴う実相対擬同型（2026-10-15）

`DeltaRootRelativeKoszul.lean`で、係数側の任意有限列a:Fin m→Aに対し、
根関係の係数付きKoszul添加写像へ標準係数像C(a_i)のKoszul操作を施した
実写像K(Ca;K(g;B⊗_A N))→K(Ca;(Q⊗_A N)[0])を構成した。
共通scalarConeFunctor_map_quasiIsoと有限帰納法により、その擬同型性を証明した。
特にa=(p,d)に適用する公開定理を供給した。
aの正則性、係数側Koszul複体の次数零集中、Nの平坦性、Aのp正則性は不要。
同等の一般Koszul保存定理や新たな複体は作らず、既存関手・実添加写像を使用した。
3公開宣言の対象3606ジョブとpure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
最初の全体ビルドは、実行中に共有ルートへ追加されたMappingConeLinearDualの
未生成oleanで失敗した。共有ファイルを編集せず、更新後の依存関係で再検証し、
全体4813ジョブ成功。全体は共有側の既存警告を含む。
具体的な根関係添加擬同型は3e3ba2cで工程別コミット済み。

次のBS専用予定`DeltaDivisionNormalizedStepKoszul.lean`で、既存有限正規化
δ関係の一段を対象とする。最高変数分離と前段商への係数変更により、
実正規化関係式がX_s^p-C(deltaDivisionFiniteNormalizedStepCoefficients_s)と
一致する図式を証明する。異なる有限個の最高段関係の弱正則性・Koszul分解と、
任意係数加群・係数側有限Koszul操作を伴う今回の相対擬同型をこの具体的段へ適用する。
正規化された通常商の計算と、δ包からの実比較に必要な既存p正則性・ghost単射・
δd単元条件を区別して明記する。通常mod(p,d)商の計算だけで完備化後のCFFは結論しない。
δ関係全段の実導来比較、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：実有限正規化δ関係の一段でのKoszul分解・相対比較（2026-10-15）

`DeltaDivisionNormalizedStepKoszul.lean`で、既存最高変数分離同型と前段実正規化商
への係数変更を合成した標準環射を供給した。下位多項式の包含像・最高段変数の
図式を証明し、実正規化関係式がX_s^p-C(前段係数_s)に一致することを証明した。
異なる有限個の最高段関係の実像について、前段商上の弱正則性と実Koszul分解を
供給した。また前段商の任意係数加群・任意有限係数列を伴う実相対添加写像の
擬同型性を、前工程の具体的根関係比較から供給した。
ここでは正規化関係の代数計算をしており、源p正則性・ghost単射・δdとの単元一致は
この計算には不要。rawδ包との既存比較にはその既存の明示仮定を別途適用する。
前段商にはp,dの像を既に課しているため、この段の相対比較だけから
raw包の係数側(p,d)導来比較を完成したとは数えない。
7公開宣言の対象3607ジョブ、pure B4監査、全体4813ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
任意係数列の相対根関係擬同型は4f06cd8で工程別コミット済み。

次のBS専用予定`DeltaDivisionNormalizedStepSourceQuotient.lean`で、次段の多項式環を
前段表示イデアルの包含像だけで割った実源商と、前段実商上の最高変数の多項式環を
具体的に同定する。既存の最高変数分離・係数商同型を合成し、標準商射の図式を証明する。
今回の実像の正則性を、この実源商内の最高段関係の正則性・有限Koszul分解へ戻す。
同等の一般係数商同型や商環の定義は重複して作らない。
全段の実導来比較、完備化/perfectionのCFF、根族付き完全忠実平坦拡大の存在、一般B4は未完成。

## B4-6：前段関係で割った実源商内の最高段関係の正則性（2026-10-15）

`DeltaDivisionNormalizedStepSourceQuotient.lean`で、次段源多項式環内の
前段表示イデアルの標準包含像を具体化した。最高変数分離でこれが
係数側の表示イデアルへ移ることを証明し、既存係数商同型を合成した。
前段関係だけで割った実源商を、前段実正規化商上の最高変数の多項式環と同定し、
標準商射が前工程の具体的多項式射に一致する図式を証明した。
この実環同型と共通の弱正則列の移送を使い、源商内の異なる有限個の
最高段関係が弱正則列であること、その実Koszul分解を証明した。
σの有限性・Aのp正則性・非零性・Noether性は不要。
前段表示イデアルには既にmod(p,d)の関係を含むため、rawδ包全体の
(p,d)導来比較や完備化後のCFFをこの証明だけで結論していない。
6公開宣言の対象3608ジョブ、pure B4監査、全体4813ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
正規化関係の標準像でのKoszul計算はa50c367で工程別コミット済み。

次のBS専用予定`DeltaDivisionNormalizedStepQuotientComparison.lean`で、
今回の実源商に最高段関係の標準像をすべて課した二重商を、既存の
次段実正規化商と同定する。既存表示イデアルの後続式とDoubleQuot同型を使用し、
標準多項式射の像の図式を明示する。同等の商環・一般二重商同型は新設しない。
有限個の最高段関係の商とKoszul分解をつなぎ、有限添字σの場合は
最高段全体の実分解を供給する。有限性はこの途中工程に限り、
任意perfectoid環・任意イデアルに関する最終B4の仮定には追加しない。
全段・任意添字の実導来比較、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：最高段全関係の二重商と次段実正規化商（2026-10-15）

`DeltaDivisionNormalizedStepQuotientComparison.lean`で、前段関係の実源商内の
最高段関係イデアルを、元の関係式イデアルの標準商射による像として具体化し、
実関係式像のspanに一致することを証明した。
既存表示イデアルの後続式とDoubleQuot同型により、最高段関係をすべて課した
二重商を既存の次段実正規化商と同定した。元の多項式の標準二重商像を
次段標準商像へ送る図式を供給した。この商比較は任意添字σで成立する。
さらに有限添字の場合、標準有限列挙による全最高段関係の実Koszul分解と、
そのspanが実際の最高段イデアルに一致することを証明した。
有限性はこの有限分解工程だけの仮定であり、最終B4の仮定へは追加しない。
7公開宣言の対象3609ジョブとpure B4監査成功。標準3公理のみ。
新sorry・公理・引用なし。実源商内の有限正則性はa9e7528で工程別コミット済み。
全体ビルドは別作業の未追跡CochainLinearDualCone.leanの92行・108行の
未解決証明で失敗した。BS対象の依存には含まれないため、共有ファイルは編集せず、
本工程は対象ビルドと依存監査を検証根拠とする。全体成功とは報告しない。

次のBS専用予定`DeltaDivisionNormalizedStepResolution.lean`で、実源商から
次段実正規化商への標準射・代数構造を、今回の二重商比較から供給する。
有限添字の全最高段Koszul複体について、零次ホモロジーを次段実商と
具体的に同定し、次段実商の単一複体への実擬同型を構成する。
一般の商写像・代数・Koszul分解の同等定義は新設せず、既存APIを使用する。
任意添字と全段の実導来比較、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：有限最高段Koszul複体から次段実商への実射影分解（2026-10-15）

`DeltaDivisionNormalizedStepResolution.lean`で、実源商から次段実正規化商への
標準射と元の多項式上の標準商射の図式を供給し、その代数構造を明示した。
既存二重商比較・有限全関係の商比較を標準実源商代数同型へ強化した。
有限最高段Koszul分解の零次ホモロジー同型とこの実商比較を合成して、
実際の次段正規化商への零次線形同型を構成した。
その同型を使った具体的添加写像、擬同型性、零次ホモロジー射の図式を証明した。
各項の有限自由性・全非零次数ホモロジー消滅と合わせ、共通IsResolutionOf APIで
実際の次段商の射影分解証明書も供給した。
代数構造と二重商比較は任意σ、有限Koszulモデルは[Fintype σ]の途中工程。
零次同型は既存Koszul分解の選択された線形同型を合成したものであり、
この添加写像の零次成分が標準環射と一致すると追加で主張してはいない。
10公開宣言の対象3610ジョブ、pure B4監査、全体4814ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
前回の共有CochainLinearDualConeの全体ビルドエラーは今回の全体検証では解消済み。
担当外のファイルは編集していない。二重商比較は1c7b06cで工程別コミット済み。

次のBS専用予定`DeltaDivisionNormalizedStepTor.lean`で、前段商Q_Nから実源商への
標準係数射を源商同型の逆と多項式Cから具体化する。
実源商→次段商の今回の標準射との合成が既存の標準一段射Q_N→Q_{N+1}に
一致する図式・スカラー塔を証明し、実源商がQ_N上平坦なことを供給する。
既存次段商のQ_N上の忠実平坦性と共通TorFlatBaseChangeVanishingから、
任意Q_N加群Mに対するTor_{>0}^源商(Q_{N+1},源商⊗_{Q_N}M)の消滅を証明する。
この段のTor計算自体にはσの有限性を要求せず、有限σでは今回の実射影分解との
比較により実最高段Koszulホモロジーへ接続する。
同等の一般Tor・代数塔定義は重複せず、既存APIと具体的標準射を使う。
任意添字・全段の実導来比較、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：実正規化一段の標準スカラー塔と任意係数加群でのTor（2026-10-15）

`DeltaDivisionNormalizedStepTor.lean`で、前段商Q_Nから実源商Sへの標準係数射を
具体化し、元の下位多項式の包含像との一致を証明した。
S→Q_{N+1}との合成が既存の標準一段射に一致する図式を供給し、三環の
標準代数構造に関するスカラー塔を証明した。源商の表示をQ_N代数同型に強化し、
SのQ_N上の自由性・平坦性を供給した。
既存Q_{N+1}のQ_N上の忠実平坦性と共通TorFlatBaseChangeVanishingから、
任意Q_N加群Mに対するTor_{>0}^S(Q_{N+1},S⊗_{Q_N}M)の消滅と
対応する実導来テンソルの次数零集中を証明した。この計算は任意σで成立する。
有限σの場合、前工程の実次段商の射影分解・共通Tor対称性・Koszul反復錐比較を
合成し、このTorと実最高段の係数付きKoszulホモロジーの同型を構成した。
その全負次数ホモロジーが零となることも証明した。
12公開宣言の対象3611ジョブ、pure B4監査、全体4820ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
実次段商の射影分解は1a90b3aで工程別コミット済み。

次のBS専用予定`DeltaDivisionWittJetRegularity.lean`で、既存の次段δ反復関係と
Witt根関係の主イデアル置換等式を、具体的な下位関係商A/Iへ移す。
p,dと下位δ反復関係がIに属し、δdに一致する単元uを明示したとき、
商内のWitt根関係が非零因子なら次段δ反復関係も非零因子となることを証明する。
主イデアルの所属・割切りと既存の正則元の積のAPIを使用し、同等の一般正則性補題は作らない。
元のδ反復関係と実正規化計算の接続であり、必要なp正則性・ghost単射を既存通り明記する。
この結果を実源商の比較へ適用し、δ反復関係の実分解へ進む。
mod(p,d)の通常商内の計算とraw包の実導来比較は区別し、
完備化/perfectionのCFF、根族付き完全忠実平坦拡大の存在、一般B4は未完成。

## B4-6：下位関係商における元のδ反復関係の正則性・導来商比較（2026-10-15）

`DeltaDivisionWittJetRegularity.lean`で、p,dと下位δ反復関係がIに属する場合、
A/I内の次段δ反復関係とWitt根関係が同じ主イデアルを生成することを証明した。
既存の主イデアル置換等式を商射で移し、主イデアル所属・割切りと既存正則元の
積のAPIにより、両関係の商内の非零因子性が同値となることを証明した。
Witt根関係が正則なら元のδ反復関係の実Koszul分解を供給し、さらに共通の
正則主イデアルの導来商APIへ適用して、元のδ反復関係による導来基底変更・
係数制限と実Koszul錐関手との自然同型を構成した。
既存HasDerivedCategory.standardを局所使用し、新たな導来圏や∞圏は構築していない。
p正則性・ghost単射・δdに一致する単元v・下位関係の所属を全て明示した。
Witt根関係の正則性は、この段のKoszul分解・導来比較では入力仮定である。
この結果は既存André引用には依存しない。
4公開宣言の対象2991ジョブ、pure B4監査、全体4820ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
実正規化一段のTor・Koszul計算は7d9d760で工程別コミット済み。

次のBS専用予定`DeltaDivisionNormalizedAmbientSource.lean`で、相対自由δ環全体に
前段の正規化関係だけを課した商を、有限実源商上の後続変数の多項式環と同定する。
既存の有限初期変数/後続変数分離と係数商同型、有限表示イデアルの包含像の等式を
合成し、標準初期多項式像の図式を証明する。δdに一致する単元条件が必要な
正規化イデアルの包含像の等式は既存通り明示する。
その後、既存のWitt逆座標の実比較を合成し、Witt根関係の正則性を元の
自由δ環の下位関係商へ戻す。今回の正則性同値でδ反復関係へ接続する。
既存p正則性・ghost単射の条件を省略せず、通常mod(p,d)商と実導来比較を区別する。
全段・任意添字の実導来比較、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：全自由環の正規化下位関係商とWitt根関係の正則性（2026-10-15）

`DeltaDivisionNormalizedAmbientSource.lean`で、有限実源商の表示イデアルの
初期包含像が、全相対自由環内の既存下位正規化イデアルに一致することを証明した。
既存初期/後続変数分離と係数商同型を合成し、全自由環の下位正規化関係商を
有限実源商上の後続変数の多項式環と同定した。
標準商射上の具体式、初期有限多項式の像が有限源商の係数像へ移る図式を供給した。
有限実源商内の次段モニック関係の正則性と係数ごとの乗法単射により、
全自由環の下位正規化商内でも、その初期包含像が非零因子となることを証明した。
σの有限性は不要。δdに一致する単元条件を既存表示イデアルの比較と同様に明示した。
この段は逆Witt座標によるrawδ関係商への移送前の実正規化環の計算。
6公開宣言の対象3609ジョブ、pure B4監査、全体4820ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
δ反復関係とWitt根関係の正則性同値は461990aで工程別コミット済み。

次のBS専用予定`DeltaDivisionFiniteJetRegularity.lean`で、既存の有限δ剰余商から
正規化商への逆Witt座標同型を使用する。
L=RelativeFreeDeltaRing σ A、I=span(p,Cd)⊔deltaDivisionFiniteRelationIdeal D d a (N+1)
を具体的な下位関係イデアルとし、L/I内のWitt根関係の像を今回の非零因子へ送る
標準商射の図式を証明する。そこからWitt根関係の正則性をL/Iへ移し、
下位δ関係の所属とδd単元の像を明示して、元のδ反復関係のN+2段の正則性・
実Koszul分解を前工程から導く。
源A・Lのp正則性、Lのghost単射、δdに一致する単元条件は既存API通り全て明記する。
σの有限性は要求しない。通常mod(p,d)商とraw包全体の実導来比較を区別し、
全段の完備化/perfectionのCFF、一般B4は未完成。

## B4-6：元の自由δ環の具体的下位関係商での次段δ関係の正則性（2026-10-15）

`DeltaDivisionFiniteJetRegularity.lean`で、
L=RelativeFreeDeltaRing σ A、I=span(p,Cd)⊔deltaDivisionFiniteRelationIdeal D d a (N+1)
を明示し、既存の逆Witt座標の商同型でL/I内のWitt根関係を
全自由環の正規化下位関係商の実モニック関係へ移した。
その実正規化計算からWitt根関係の非零因子性をL/Iへ供給した。
下位δ関係のIへの所属、p,dの所属、δdに一致する単元の係数像を明示し、
元のN+2段のδ反復関係そのものがL/Iで非零因子となることを証明した。
その実Koszul分解と、元の次段δ関係による導来商と実Koszul錐関手との
自然同型も共通APIから供給した。
σの有限性は不要。源A・Lのp正則性、Lのghost単射、δd単元条件は全て明示した。
Witt根関係の正則性を追加仮定として受け取らず、正規化計算から供給している。
対象はmod(p,d)を課した具体的下位関係商であり、raw包全体のCFFとは区別する。
4公開宣言の対象3791ジョブ、pure B4監査、全体4820ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
全自由環の正規化源商の比較は0f6253aで工程別コミット済み。

次のBS専用予定`DeltaDivisionFiniteJetSubset.lean`で、同じ下位イデアルIに
任意の先行添字集合T⊆σのN+2段δ関係だけを追加する。
既存族の主イデアル置換等式により追加δ関係をWitt関係へ移し、逆座標と
今回の源商比較で既存部分根関係イデアルへ結ぶ図式・商同型を供給する。
Tに属さない添字の次段δ関係の正則性を、部分根関係商の正則性から導く。
これにより次段δ関係の有限族の弱正則性・実Koszul分解へ進む。
単独関係の正則性だけから同時族の弱正則性は推論しない。
必要なp正則性・ghost単射条件は維持し、任意添字と全段の実導来比較、
完備化/perfectionのCFF、一般B4は未完成。

## B4-6：任意の同段先行部分集合のδ関係を課した実商の正則性（2026-10-15）

`DeltaDivisionFiniteJetSubset.lean`で、元の下位δ関係商を、最高変数・後続変数を
分離した実多項式環へ送る同型を構成し、Witt根関係が実モニック根関係の係数像へ
移る図式を証明した。任意T⊆σについて、次段δ関係のT部分族とWitt関係の
T部分族が同じ下位商イデアルを生成することを既存の族置換等式から証明した。
この部分族イデアルを既存部分根関係イデアルの係数包含像へ移し、
追加δ関係を課した実商を、部分根関係商上の後続多項式環と同定した。
残るWitt関係の標準像の図式、T外のWitt関係の非零因子性を供給し、
同じ主イデアルを生成することと割切り・正則な積のAPIから、T外の
元の次段δ関係の非零因子性も証明した。
T・σの有限性は不要。源A・Lのp正則性、Lのghost単射、δd単元条件は維持した。
8公開宣言の対象3792ジョブ、pure B4監査、全体4830ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
単独の次段δ関係の正則性は511f03aで工程別コミット済み。

次のBS専用予定`DeltaDivisionFiniteJetFamilyRegularity.lean`で、重複のない
有限添字列の各先行部分をTとして今回の結果に適用する。
元の下位δ関係商内のN+2段δ関係の有限列が弱正則となること、
Fin m→σの単射で指定する有限族の実Koszul分解を証明する。
有限添字σの場合は全同段関係の実分解へ適用するが、最終B4の仮定へ有限性は追加しない。
共通の弱正則列・Koszul分解APIを使い、同等の一般述語・分解定義は作らない。
通常mod(p,d)商内の計算とraw包全体の実導来比較は区別する。
全段・任意添字の完備化/perfectionのCFF、一般B4は未完成。

## B4-6：元の同段δ関係の有限族の弱正則性と実Koszul分解（2026-10-15）

`DeltaDivisionFiniteJetFamilyRegularity.lean`で、具体的下位関係商内の
元のN+2段δ関係の有限列の生成イデアルを、添字部分集合の関係イデアルと同定した。
重複のない有限列の各先行部分に前工程の任意部分集合での正則性を適用し、
同段δ関係の有限列全体の弱正則性を証明した。Fin m→σの単射で指定する族へ移送し、
共通APIによる実Koszul分解を供給した。
有限σの場合は全同段関係にも適用し、有限列挙の生成イデアルが全同段関係の
標準像のspanに一致することも証明した。一般の有限族についてσの有限性は不要。
源A・Lのp正則性、Lのghost単射、δd単元条件は維持した。
6公開定理の対象3793ジョブ、pure B4監査、全体4830ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
任意同段部分集合での正則性は369a082で工程別コミット済み。

次のBS専用予定`DeltaDivisionFiniteJetStepResolution.lean`で、元の下位関係商
L/(span(p,Cd)⊔finiteRelations(N+1))に全同段δ関係を課した二重商を、
既存finiteRelationIdeal_succとDoubleQuot同型で
L/(span(p,Cd)⊔finiteRelations(N+2))へ同定し、標準商射の図式を供給する。
商比較は任意σで成立する形にし、有限σの場合は今回の全同段Koszul分解の
零次ホモロジーをこの実次段商へ移し、具体的擬同型・共通IsResolutionOfを構成する。
既存の環・商・分解APIを再利用し、同等の一般定義は重複しない。
有限性を最終B4の仮定に追加せず、通常mod(p,d)商とraw包全体の実導来比較を区別する。
全段・任意添字の完備化/perfectionのCFF、一般B4は未完成。

## B4-6：元の有限δ関係の次段実商への実Koszul射影分解（2026-10-15）

`DeltaDivisionFiniteJetStepResolution.lean`で、元の下位δ関係商内の全同段関係の
spanを元のイデアルの標準商像と同定し、既存有限関係イデアルの後続式と
DoubleQuot同型から、全同段関係を課した二重商を元の次段実商
L/(span(p,Cd)⊔finiteRelations(N+2))へ同定した。
標準自由環の商射との図式・下位商から次段商への標準射・代数構造を供給した。
これらの商比較・環射は任意σで成立する。
有限σでは、前工程の元の全同段Koszul分解の零次同型を、この実次段商への
標準下位商代数同型と合成した。次段実商の単一複体への具体的添加写像と
擬同型性、共通IsResolutionOf APIでの実射影分解証明書を供給した。
零次線形同型は既存Koszul分解の選択を使用し、その添加写像の零次成分が
標準環射と一致するとは追加で主張していない。
源A・Lのp正則性、Lのghost単射、δd単元条件は分解に明示した。
13公開宣言の対象3794ジョブ、pure B4監査、全体4830ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
元の有限同段δ関係の弱正則性はc2de0d8で工程別コミット済み。

次のBS専用予定`DeltaDivisionFiniteJetStepComparison.lean`で、元の下位商と次段商を
既存逆Witt座標で実正規化側へ移し、同じN+2初期/後続変数分離を用いた表示を供給する。
下位商は後続多項式環の係数として有限実源商、次段商はその係数として
有限次段実正規化商を持つ形にし、今回の元の段間標準射が
既存deltaDivisionNormalizedStepNextMapの後続多項式係数変更に一致する図式を証明する。
既存正規化側の標準スカラー塔・Tor消滅へ実際の環射を両立させて接続するための比較である。
任意σを許し、有限性を最終B4に追加しない。通常mod(p,d)商とraw包全体の実導来比較を区別する。
全段の完備化/perfectionのCFF、一般B4は未完成。

## B4-6：元のδ段間標準射と正規化側標準射の実比較（2026-10-15）

`DeltaDivisionFiniteJetStepComparison.lean`で、同じN+2初期/後続変数分離により、
全自由環の次段正規化商を有限次段実商上の後続多項式環と同定した。
既存逆Witt座標の商同型を合成し、元の下位δ関係商は有限実源商上の
後続多項式環、元の次段商は有限次段実正規化商上の後続多項式環へ移した。
両側の標準商射上の式を供給し、元の段間標準射が
MvPolynomial.map(deltaDivisionNormalizedStepNextMap)に一致する可換図式を証明した。
逆座標と変数分離が両側で共通であることを使い、実際の環射を両立させている。
σの有限性は不要。p正則性・ghost単射・δd単元条件を既存通り明示した。
8公開宣言の対象3797ジョブ、pure B4監査、全体4836ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
元の実次段商の射影分解は7702504で工程別コミット済み。

次のBS専用予定`DeltaDivisionFiniteJetStepScalarTower.lean`で、前段有限正規化商Q_Nから
元の下位δ関係商・次段商への標準係数射を今回の同型の逆から具体化する。
下位商の係数射と元の段間射との合成が次段商の係数射に一致する図式と、
標準代数構造のスカラー塔を証明し、既存多項式表示・正規化側の平坦性から
元の下位商・次段商のQ_N上の平坦性を供給する。
続くBS専用予定`DeltaDivisionFiniteJetStepTor.lean`で、共通TorFlatBaseChangeVanishingから
任意Q_N加群Mに対するTor_{>0}^下位商(次段商,下位商⊗_{Q_N}M)の消滅を供給する。
有限σでは元のδ関係の実射影分解を用いたKoszulホモロジー比較へ接続する。
同等の一般代数塔・Tor定義は作らず、既存APIと具体的標準環射を使用する。
通常mod(p,d)商とraw包全体の実導来比較は区別し、
全段の完備化/perfectionのCFF、一般B4は未完成。

## B4-6：元のδ段間射の標準係数射・スカラー塔と自由性（2026-10-15）

`DeltaDivisionFiniteJetStepScalarTower.lean`で、前段有限正規化商Q_Nから
元の下位δ関係商R_Nと次段商R_{N+1}への標準係数射を比較同型の逆から具体化した。
元の段間射と係数射の合成が次段係数射に一致する図式を証明し、
既存の段間標準代数構造と両係数代数構造のスカラー塔を供給した。
両商の比較をQ_N代数同型へ強化し、既存の正規化側自由性と多項式係数基底から
元の両商が標準係数射によってQ_N上自由・平坦となることを証明した。
σの有限性は不要。p正則性・ghost単射・δd単元条件は既存通り明示した。
12公開宣言の対象3799ジョブ、pure B4監査、全体4836ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
元の段間射の実比較はee0eebcで工程別コミット済み。

次は登録済み`DeltaDivisionFiniteJetStepTor.lean`で、この標準塔と平坦性を用いて
元の段間射に関する実Tor消滅・有限添字の実Koszulホモロジー比較を検証する。
通常mod(p,d)商とraw包全体の実導来比較は区別し、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：元のδ段間射の実Tor消滅と係数付きKoszul比較（2026-10-15）

`DeltaDivisionFiniteJetStepTor.lean`で、前工程の標準スカラー塔と両商の係数環上の
平坦性から、共通TorFlatBaseChangeVanishingを使い、任意Q_N加群Mに対する
Tor_{>0}^R_N(R_{N+1},R_N⊗_{Q_N}M)の消滅を証明した。
対応する実DerivedTensorの次数零集中も供給した。これらにはσの有限性は不要。
有限σでは、元の全同段δ関係の実射影分解・共通Tor対称性・Koszul反復錐比較を
合成し、実Torと元の係数付きKoszulホモロジーを同定し、全負次数の消滅を証明した。
源A・Lのp正則性、Lのghost単射、δd単元条件は明示した。
4公開宣言の対象3800ジョブ、pure B4監査、全体4836ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。全体は共有側の既存警告を含む。
標準スカラー塔・係数環上の自由性はf6cfc84で工程別コミット済み。

### 原典に照らした次工程の固定

著者公開版Definition 2.42・Corollary 2.44（pp.26–27）、Prop.3.13の証明（pp.34–35）を
再確認した。相対完全正則性は係数側Koszul複体を伴う条件であり、今回のmod(p,d)を
既に課した通常商のTor計算だけでは、rawδ包の導来(p,d)完備化後のCFFを結論できない。
原典は自由δ環のFrobeniusの(p,z)完全忠実平坦性と、p除算包・分冪比較を用いている。
この未解決境界を省略せず、以下の原典入力を進める。

次のBS専用予定`FreeDeltaFrobeniusCoordinateResidueFlat.lean`で、既存
FreeDeltaFrobeniusModPFlatの実mod p Frobeniusの忠実平坦性を使う。
自由整数δ環L=FreeDeltaRing σの指定変数z=X_(s,0)に対し、
L/(p,z)からL/(p,φ(z))への実誘導射を、mod p Frobenius作用の環の係数商として表示し、
既存の忠実平坦基底変更でその通常忠実平坦性を証明する。
剰余Frobeniusのφ(z)像をz^pに移す図式も明示する。
続いて(p,z)と(p,φ(z))の正則性・既存Koszul/Tor判定を組み合わせ、
この具体的自由δ環射の完全平坦性、実完備化との比較へ進む。
一般のFrobeniusや完全平坦性の同等定義は新設しない。
原典のp除算・分冪経路、raw包全体の実導来比較、完備化/perfectionのCFF、一般B4は未完成。

## B4-6：自由δ Frobeniusの指定変数商の実忠実平坦性（2026-10-15）

`FreeDeltaFrobeniusCoordinateResidueFlat.lean`で、自由整数δ環Lと任意の指定変数
z=X_(s,0)について、具体的な通常射L/(p,z)→L/(p,φ(z))を構成し忠実平坦性を証明した。
実mod p Frobenius作用の環をzの像のイデアルで基底変更し、二重商同型で両側を移送した。
元の自由環の標準商射上でφと両立する式と、φ(z)≡z^p mod pの式を供給した。
σの有限性を要求しない。12公開宣言の対象3217ジョブ、pure B4監査、全体4836ジョブ成功。
標準3公理のみ。新sorry・公理・引用なし。全体の共有既存sorry警告は別扱い。
この通常商の結果から完備化後の完全忠実平坦性を直接結論しない。

次のBS専用予定`FreeDeltaFrobeniusCoordinateRegular.lean`で、L/p上のzとφ(z)の
正則性、およびL上の(p,z)と(p,φ(z))の弱正則性を証明する。
標準mod p同型・既存多項式変数の正則性と既存弱正則列APIを再利用する。
共通要求G3の主元Tor判定は現時点で未受領。この適用だけを保留し、正則性の独立入力を進める。
p除算・分冪比較、raw包全体の導来完備化/perfectionのCFF、一般B4は未完成。

## B4-6：自由δ Frobeniusの正則対・実Koszul分解・実剰余Tor（2026-10-15）

`FreeDeltaFrobeniusCoordinateRegular.lean`で、自由整数δ環Lの指定変数zについて、
L/p上のzとφ(z)の正則性、L上の(p,z)と(p,φ(z))の弱正則性を証明した。
既存IsKoszulResolutionとその正則列からの構成に接続し、両対の実Koszul分解を供給した。
さらに既存torAlgKoszulEquivを実Frobeniusφへ適用し、
任意i>0についてTorAlg φ i (L/span{p,z})がSubsingletonとなることを証明した。
標準商の型は二元生成イデアルの通常商そのもので、σの有限性を要求しない。
7公開定理の対象3465ジョブ、pure B4監査、全体4837ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有側の既存sorry警告は別扱い。
通常剰余の忠実平坦性はe8e48a2で工程別コミット済み。

今回のTor消滅は試験加群L/(p,z)に対するもので、全ての(p,z)零化加群への
IsCompletelyFlatの結論をまだ含まない。共通要求G3の適用と実完備化比較は未完成。
次は原典Prop.3.13のp除算の具体的な係数の単元性・分冪比較の入力を調べる。
既存isDistinguished_factor（原典Lemma 2.24）を再利用し、同じ一般単元補題は作らない。
新規モジュールが必要になれば、使用する具体的候補・完備性条件と予定名を先に登録する。
古典的候補を実導来候補と無条件に同一視しない。
raw包全体の導来完備化/perfectionのCFF、必要な根付きCFF拡大、一般B4は未完成。

## B4-6：次工程の登録（2026-10-15）

BS専用予定`DeltaPTorsionReduction.lean`：pの冪の分母集合はφで安定なので、既存δ局所化から
ker(A→A[1/p])がδ安定であることを証明する。そのδ閉包は元の核に等しく、
既存のδねじれ除去商はp正則となる。一般δ環の結果で、共通のTor・完備性定義は増やさない。
これを具体的なDeltaDivisionTorsionQuotient D p aへ適用する。

続くBS専用予定`DeltaPDivisionUnit.lean`：p除算添加変数の標準像とpとの積が
指定元の像に等しい式を、既存の古典的完備化候補へ移す。
同候補のpのJacobson根基への所属をMathlibの完備化APIから供給し、
指定元がdistinguishedなら除算変数像は単元となることを既存isDistinguished_factorで証明する。
この古典的結果を実導来候補へ転用する際は別途比較を証明する。
原典の分冪包との比較・完全忠実平坦性をこの単元計算だけから結論しない。

## B4-6：p冪ねじれのδ安定性とp除算前完備候補のp正則性（2026-10-15）

`DeltaPTorsionReduction.lean`で、pの冪の分母集合のφ安定性を証明し、既存δ局所化により
ker(A→A[1/p])のδ安定性とそのδ閉包の一致を供給した。
商から局所化への既存kerLiftの単射性とpの像の単元性から、δねじれ除去商のp正則性を証明した。
具体的な既存DeltaDivisionTorsionQuotient D p aにも適用した。
任意σと一般のδ環Aを許す。完備化後の新ねじれの不存在はこの結果に含めない。
6公開定理の対象2063ジョブ、pure B4監査、全体4837ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。

次は登録済みDeltaPDivisionUnitの古典的候補の単元係数を検証する。
G3による自由δ Frobeniusの完全平坦性、p除算・分冪包の比較、
完備化/perfectionのCFF、一般B4は未完成。

## B4-6：具体的古典的p除算候補の単元係数と完備性（2026-10-15）

`DeltaPDivisionUnit.lean`で、既存ClassicalDeltaDivisionCompletion D p aについて
完備化イデアルがp主イデアルであることを確認し、同候補のp進完備性とp正則性を証明した。
正則性には5c0c849の旧ねじれ除去商の結果と共通AdicCompletionRegularを使用した。
この候補自身の導来p完備性は、証明したp正則性を明示して既存AdicComparisonから得た。

p除算変数の具体的標準像u_sを定義し、p*u_s=j(a_s)を証明した。
pのJacobson根基への所属をMathlibの完備化APIから供給し、既存Lemma 2.24を適用して
D.IsDistinguished(a_s)ならu_sが単元であることを証明した。環・標準射・単元係数を
明示した存在定理も公開した。任意σ、一般δ環Aを許す。
9公開宣言の対象2829ジョブ、pure B4監査、全体4837ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。
この古典的候補自身の導来完備性と、原典の実導来完備化候補との比較は区別する。
実候補との同型・分冪包比較・完全忠実平坦性・一般B4は未完成。

### 共通基盤への要求 G6：導来完備環の完備化元はJacobson根基に属する（2026-10-15送信済み）

対象：可換環T:Type u、a:T、
h:IsModuleComplete T a (ModuleCat.of T T)。結論：a∈Ideal.jacobson (⊥:Ideal T)。
p正則性・有界ねじれ・古典的完備性・Noether性・有限生成性は仮定しない。
利用：B4-6、実DerivedDeltaDivisionCompletion D p a内のdistinguished除算係数の単元性。
不足：既存の古典的IsAdicComplete.le_jacobson_botはあるが、一般の導来完備環には
無条件の古典的比較を適用できない。現在の共通公開APIではこの導来入口を確認できなかった。
既存の列漸化式の全単射判定から幾何級数を構成する方向が候補で、BS内に同等の一般補題を作らない。
待つ工程：実導来候補に対するこのJacobson入力のみ。
独立作業：以下の実raw除算環の座標変換と、分冪比較の代数的入力を進める。
外部チャットへの依頼メッセージは送っていない。

次のBS専用予定`DeltaPDivisionFrobeniusShift.lean`で、任意元族y_sについて
raw δ添加環A{φ(y_s)/p}とA{y_s^p/p}の具体的δ環同型を構成する。
φ(y)=y^p+p*δyから除算変数をδyだけ平行移動し、既存の指定解付きδ除算普遍性で
両方向の標準射と逆性を証明する。基底射と除算変数上の式を保持する。
これは原典Cor.2.39の分冪比較へ進むための座標整理であり、分冪構造の存在や平坦性とは区別する。
G3、G6に依存しない。新しい一般導来完備化・Tor・完全平坦性定義は作らない。

## B4-6：rawδ p除算のFrobenius平行移動同型（2026-10-15）

`DeltaPDivisionFrobeniusShift.lean`で、任意元族y_sについて
A{φ(y_s)/p}→A{y_s^p/p}を除算変数v_s↦w_s+j(δy_s)で構成し、
逆方向をw_s↦v_s−j(δy_s)で構成した。既存の指定解付きδ添加普遍性により両射の一意性、
δ構造・基底射との両立、両合成の恒等性を証明し、具体的な環同型として公開した。
初期除算変数上の両方向の式を保持する。Aのp正則性・完備性・σの有限性は不要。
13公開宣言の対象2059ジョブ、pure B4監査、全体4843ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。
raw添加環の結果を導来pushoutの離散性や分冪構造の存在とは同一視しない。

次のBS専用予定`DeltaPDivisionFrobeniusShiftTorsion.lean`で、この平行移動を
既存DeltaDivisionTorsionQuotient D p (φ∘y)とD p (y^p)へ移す。
具体的な両標準基底射と可除性・既に証明した対象のp正則性を供給して
既存existsUnique_deltaDivisionTorsionHomを適用し、基底射を保つ具体的δ環同型を構成する。
続くBS専用予定`DeltaPDivisionFrobeniusShiftDerived.lean`では、共通の実PDCompletionH0と
既存δ完備化一意延長を使用して、両実DerivedDeltaDivisionCompletion D p (...)間へ同型を移す。
pを除数とするため両完備化元の像は同じpであり、既存の実p導来完備性をそのまま適用する。
古典的完備化への置換を経ずに、実H⁰の標準単位との図式とδ両立を証明する経路を優先する。
G3・G6の一般入力はこの移送には不要。実候補の単元係数に対するG6の待ちと区別する。
分冪包比較・完全忠実平坦性・一般B4は未完成。

## B4-6：p除算平行移動の旧ねじれ除去商への移送（2026-10-15）

`DeltaPDivisionFrobeniusShiftTorsion.lean`で、既存DeltaDivisionTorsionQuotientの
φ(y_s)/p側とy_s^p/p側の間に、元の基底射を保つ具体的δ環同型を構成した。
raw平行移動の標準射と既存関係式から対象内の可除性を供給し、証明済みのp正則性と
既存existsUnique_deltaDivisionTorsionHomを適用した。両方向のδ両立・基底両立と
普遍性による逆性を公開した。一般δ環・任意σを許す。
11公開宣言の対象2335ジョブ、pure B4監査、全体4845ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有側の既存警告は別扱い。
raw同型は5217fc2で工程別コミット済み。

次は登録済みDeltaPDivisionFrobeniusShiftDerivedで、既存の実導来完備化H⁰へ移し、
元のねじれ除去商からの標準単位と元の基底射の両方との図式を証明する。
古典的完備化への置換・G3・G6はこの移送には使わない。
分冪包比較・導来pushoutの離散性・必要なCFF拡大・一般B4は未完成。

## B4-6：p除算平行移動の実導来完備化H⁰への直接移送（2026-10-15）

`DeltaPDivisionFrobeniusShiftDerived.lean`で、既存の実DerivedDeltaDivisionCompletion D p (...)
のφ(y_s)/p側とy_s^p/p側の間に、具体的なδ環同型を構成した。
旧ねじれ除去商の両射を既存existsUnique_deltaPDCompletionHomで延長し、
実p導来完備性と標準単位の一意延長によって逆性を証明した。
同型の両方向のδ両立、旧ねじれ除去商からの実Koszul標準単位との図式、
元のAからの基底射との図式を公開した。A・σ:Type uで一般δ環と任意元族を許す。
古典的完備化への置換を行わず、追加のp正則性・有界ねじれ仮定も使わない。
12公開宣言の対象2880ジョブ、pure B4監査、全体4845ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。
旧ねじれ除去商の同型はf6c6ac0で工程別コミット済み。

この実H⁰の比較は、原典Cor.2.39の導来δpushoutの離散性や分冪包との同型をまだ含まない。
次は原典Lemma 2.38・Cor.2.39のp正則性入力へ戻り、φ(y)/p（同値にy^p/p）の
実有限関係商で、関係式をmod pに移したときの正則性を既存の剰余表示と照合する。
既存共通AdicRegularQuotient.isSMulRegular_quotient_span_of_regular_modを再利用し、
mod pでの関係式の正則性から有限通常商に新しいpねじれが生じない工程を進める。
これはδ閉包前の有限通常商・実δ包・導来完備化の三者を区別する作業で、
新規ファイルが必要になれば具体的な最初の商と仮定を確定してから予定名を登録する。
G3・G6は未受領のまま。原典の分冪包比較、raw包の実導来比較、CFF根付き拡大、一般B4は未完成。

## B4-6：最初のp除算関係のp正則性工程の登録（2026-10-15）

次のBS専用予定`DeltaPDivisionFirstRelationRegular.lean`で、L=RelativeFreeDeltaRing σ A、
任意s:σ、g_s=deltaDivisionIteratedRelation D p (φ∘y) s 0を対象とする。
Aのp正則性と、y_sのA/p上の正則性を明示する。
実mod p像g_s=−(C y_s)^pを証明し、既存FlatRegularQuotientで係数側の正則性を移して
L/p上のg_sの正則性を得る。共通AdicRegularQuotientを適用し、
具体的な通常商L/span{g_s}のp正則性を証明する。(p,g_s)の実Koszul分解へも接続する。
任意σを許すが、この最初の工程は単独の指定関係式の結果であり、
全元族の関係商やδ閉包商のp正則性をこの結果だけから結論しない。
A/pのNoether性・局所性・完備性は要求しない。
一般の正則列の冪に対する既存RegularSequencePowersはNoether局所仮定を持つため、
その有限族版を一般環へ無条件に適用しない。
この工程はG3・G6を待たず進める。分冪比較・CFF・一般B4は未完成。

## B4-6：実最初のp除算関係の正則性と新pねじれの不存在（2026-10-15）

`DeltaPDivisionFirstRelationRegular.lean`で、L=RelativeFreeDeltaRing σ A、
g_s=p*X_(s,0)−C(φ(y_s))の実mod p像が−(C y_s)^pとなることを証明した。
Aのp正則性とy_sのA/p上の正則性から、共通FlatRegularQuotientを使って
L/p上のg_sの正則性を供給し、共通AdicRegularQuotientによって
実通常商L/span{g_s}のp正則性を証明した。(p,g_s)の弱正則性と実Koszul分解も供給した。
任意σ・指定sを許す。A/pのNoether性・局所性・完備性は不要。
5公開定理の対象2672ジョブ、pure B4監査、全体4846ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。
この結果はδ閉包前の単独の指定関係式に関するもので、全関係商の結果とは区別する。

次のBS専用予定`DeltaPDivisionSecondRelationRegular.lean`で、同じ指定sの
最初のδ像g'_s=δ(g_s)を加える工程を扱う。
L/(p,g_s)を既存の係数商多項式環へ移し、g'_sの像が
X_(s,0)^p−C(δφ(y_s))というモニック冪関係になることを証明する。
δ(p)≡1 mod pと既存のdeltaRootRelation_isSMulRegularを再利用する。
既存二重商同型と最初の通常商のp正則性を組み合わせ、
L/(g_s,g'_s)に新しいpねじれが生じないことを証明する。
この第二δ関係の剰余正則性自体にはAのp正則性やy_sの正則性を要求しない。
全δ段への移行、分冪比較、CFF根付き拡大、一般B4は未完成。

## B4-6：最初のδ像を加えた実通常商のp正則性（2026-10-15）

`DeltaPDivisionSecondRelationRegular.lean`で、指定した一つの初期関係g_sについて、
L/(p,g_s)を係数商A/(p,φ(y_s))上の多項式環と比較した。
既存δ差公式とδ(p)≡1 mod pから、δ(g_s)の実剰余像が
X_(s,0)^p−C(δφ(y_s))となる式を証明した。
既存deltaRootRelation_isSMulRegularを適用し、この最初のδ像の剰余正則性を得た。
この剰余正則性自体にはAのp正則性・y_sの正則性・完備性を要求しない。

二重商の標準元上の図式を証明して、最初の関係商のmod pへ移送した。
Aのp正則性とy_sのA/pでの正則性を明示し、共通AdicRegularQuotientを合成して
実通常商L/span{g_s,δ(g_s)}のp正則性を証明した。任意σ・指定sを許す。
9公開宣言の対象3533ジョブ、pure B4監査、全体4917ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。
最初の実関係商のp正則性はba322c3で工程別コミット済み。

次のBS専用予定`DeltaPDivisionFiniteStageRegular.lean`で、σ=PUnitの一元p除算について
既存deltaDivisionFiniteRelationIdeal D p (fun _↦φ(y)) Nの全Nの通常商を対象とする。
N=0,1を今回の単独関係・二関係商へ同定し、N≥2では
既存deltaDivisionFiniteNextJet_quotient_isSMulRegularの実mod(p,d)正則性をd=pに特殊化する。
既存二重商を介して前段通常商のmod pへ移し、共通AdicRegularQuotientで帰納する。
源Aのp正則性、yのA/pでの正則性、δ(p)を表す単元v、既存Witt正規化が必要とする
自由δ環のghost単射を中間入力として明示する。後二者を未証明のまま消さない。
全Nの後、既存δ閉包=iSup有限関係イデアルの表示を用いてraw一元δ包のp正則性へ進む。
PUnitの中間結果を任意元族のCFF拡大と同一視しない。
G3・G6、分冪包比較、実導来pushoutの離散性、CFF根付き拡大、一般B4は未完成。

### raw一元δ包への移行予定の登録（2026-10-15）

BS専用予定`DeltaPDivisionRawRegular.lean`で、全有限段のp正則性から
既存δ閉包=iSup有限関係イデアルの表示を使い、pに関する飽和性を証明する。
これにより一元rawδ添加環A{φ(y)/p}のp正則性を供給する。
既存の旧pねじれ除去イデアルが零となることを確認し、rawδ包と
既存DeltaDivisionTorsionQuotient D p (fun _↦φ(y))を標準射を保つδ環同型で結ぶ。
添字は任意の[Unique σ]を持つσ:Type uで実装する（PUnitを含む同じ一元の工程）。
源のp正則性、yのmod p正則性、単元δ(p)、自由δ環のghost単射を中間仮定として明示する。
任意元族のCFFや、raw包の導来pushoutとの一致をこの結果だけから結論しない。

## B4-6：一元p除算の全有限実関係商のp正則性（2026-10-15）

`DeltaPDivisionFiniteStageRegular.lean`で、一元（[Unique σ]、σ:Type u）について
既存deltaDivisionFiniteRelationIdeal D p (fun _↦φ(y)) Nの全Nの通常商のp正則性を証明した。
深さ0・1を既存の最初の関係商・二関係商に同定し、二重商比較を通して
既存の次段実δ関係のmod(p,d)正則性（d=p）を前段通常商のmod pへ移した。
共通AdicRegularQuotientで次の通常関係商へ帰納した。
Aのp正則性、yのA/pでの正則性、単元v=δ(p)、自由δ環のghost単射を明示した。
[Unique σ]はPUnitを含む同じ一元入力で、任意元族の結論ではない。
7公開宣言の対象3803ジョブ、pure B4監査、全体4917ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存警告は別扱い。
次は登録済みDeltaPDivisionRawRegularで、δ閉包へのp飽和性・raw包のp正則性、
既存旧ねじれ除去商との標準射を保つδ環同型を検証する。
分冪包比較、実導来pushoutの離散性、CFF根付き拡大、一般B4は未完成。

## B4-6：raw一元δ p除算包のp正則性と旧ねじれ除去の冗長性（2026-10-15）

`DeltaPDivisionRawRegular.lean`で、全有限段の通常商のp正則性と既存のδ閉包=iSup有限関係
イデアルの表示から、実δ閉包のp飽和性を証明した。
rawδ添加環A{φ(y)/p}自体のp正則性を得て、旧p局所化核とそのδ閉包が零であることを証明した。
既存DeltaDivisionTorsionQuotientへの標準商射を具体的な環同型へ強化し、
その値・両方向のδ両立・元の基底射との可換図式を公開した。
既存平行移動同型を使ってA{y^p/p}側のraw p正則性も供給した。
源Aがp進完備な入口では、既存Jacobson根基判定とD.isDistinguished_pから
δ(p)の単元性を内部で供給した（自由δ環のghost単射は引き続き明示する）。

[Unique σ]の一元入力で、Aのp正則性、yのA/p正則性、
自由δ環のghost単射、単元δ(p)（または源のp進完備性）を明示した結果。
10公開宣言の対象3807ジョブとpure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
全体ビルドは共有並行作業のCubicActionBasicのHasBinaryBiproduct未解決と
TensorSquareMixedSplittingのCochainBiproduct.olean不足で失敗した。
失敗ログは/tmp/bs-p-raw-regular-full.log。担当外は変更していない。
全有限段の工程は10987fdでコミット済み（同工程時の全体4917ジョブは成功）。

次のBS専用予定`DeltaPDivisionLocalization.lean`で、一般δ環Aと元族a_sについて、
raw p除算添加環B=A{a_s/p}のp局所化とA[1/p]を標準基底射を保つδ環同型で比較する。
既存δ局所化と、pの像が単元である終域への既存δ除算普遍性を再利用する。
この局所化比較自体には元族の有限性・正則性・完備性を要求しない。
続くBS専用予定`DeltaPDivisionRawEmbedding.lean`で、一元a=φ(y)の今回のraw p正則性を使い、
B→A[1/p]の具体的なδ射の単射性と、除算変数がφ(y)/pへ送られる式を証明する。
原典Cor.2.39・Warning 2.41のA[1/p]内の部分環表示へ進むための工程であり、
この埋め込みだけで分冪包との一致・完全忠実平坦性を結論しない。
分冪包比較、実導来pushoutの離散性、CFF根付き拡大、一般B4は未完成。

## B4-6：一般元族のp除算包のp局所化同型（2026-10-15）

`DeltaPDivisionLocalization.lean`で、一般δ環Aと任意元族a_sについて、
raw p除算包B=A{a_s/p}からA[1/p]への具体的δ評価を構成し、
基底射と初期除算変数a_s/pの像を明示した。
既存δ局所化の一意延長で両p局所化間のδ射を構成し、
B[1/p]≃A[1/p]の両方向のδ両立、両標準基底射との図式、逆性を証明した。
rawδ評価とA[1/p]→B[1/p]の合成が標準p局所化射となる式も供給した。
この結果は元族の正則性・有限性・完備性を要求しない。
18公開宣言の対象2064ジョブ、pure B4監査成功。全体ビルドは別途実行中。
標準3公理のみ、新sorry・公理・引用なし。
次は登録済みDeltaPDivisionRawEmbeddingの単射性と具体的像部分環表示を検証する。
分冪包比較・実導来pushoutの離散性・CFF根付き拡大・一般B4は未完成。

## B4-6：raw一元δ包のA[1/p]への具体的埋め込みと像部分環（2026-10-15）

`DeltaPDivisionRawEmbedding.lean`で、一般元族のraw包Bがp正則であれば、
具体的δ評価deltaPDivisionToAway D aが単射となることを証明した。
前工程の局所化比較と、p冪ねじれの不存在から標準局所化射の単射性を使った。
一元a=φ(y)について19c45e1のraw p正則性を供給し、実際の像部分環との環同型と
元の係数の標準像を保つ式を公開した。像のδ安定性も証明した。
一般元族y_sのφ(y_s)/pからδ(y_s)を引いた元が、A[1/p]内でy_s^p/pへ写る式を証明した。
源がp進完備な入口では単元δ(p)の指定を内部で供給する。ghost単射は引き続き明示する。
8公開宣言の対象3812ジョブ、pure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
今回の全体ビルドは共有KoszulCubeFourierModelClass.lean:38のrewrite失敗で終了した。
ログは/tmp/bs-p-localization-full.log。担当外を修正していない。
局所化工程77c037eで「実行中」と記録した全体ビルドの最終状態もこの失敗である。
分冪包との一致・実導来pushoutの離散性・CFF根付き拡大・一般B4は未完成。

### 次の代数入力の登録

BS専用予定`DeltaPDivisionWittResidueSolution.lean`で、通常環射q:A→Bとq(y)=0に対し、
既存deltaWittGhostVector D yをqで移したWitt元の係数を一段ずらした具体的Witt元tを構成する。
既存Witt Frobenius/Verschiebung恒等式と既存deltaWittGhostVector_frobeniusを使い、
p*t=WittVector.map q (deltaWittGhostVector D (φ(y)))を全Witt係数で証明する。
源Aのghost単射を明示し、終域Bのδ構造や完全性は要求しない。
源がp正則なら第0係数t_0=q(δy)も既存の低次係数APIから供給する。
これはq:A→A/(p,y)を含む具体的なWitt p除算方程式の解である。
この段階でrawδ包→A/(p,y)の環射や分冪包比較を得たとはしない。
全δ反復関係を消す通常評価への移送は、既存の逆Witt座標・関係イデアル比較で
別途確認する候補工程とし、成立の検証前に代替経路を採用したとは数えない。

## B4-6：通常剰余射に沿う具体的Witt p除算解（2026-10-15）

`DeltaPDivisionWittResidueSolution.lean`で、通常環射q:A→Bとq(y)=0に対し、
s_D(y)の像の係数を一段ずらした具体的t∈WittVector p Bを構成した。
V(t)=WittVector.map q(s_D(y))を全係数で証明し、既存Frobenius/Verschiebung恒等式と
既存deltaWittGhostVector_frobeniusからp*t=WittVector.map q(s_D(φ(y)))を証明した。
源のpをs_D(p)で表す同じ方程式と全Witt係数での関係式も公開した。
源がp正則ならt_0=q(δy)となる。源Aのghost単射を明示する。
A,B:Type u、終域Bのδ構造・完全性・標数pは要求しない。
7公開宣言の対象2062ジョブ、pure B4監査、全体4924ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。
先の全体ビルドの共有側失敗は今回の全体ビルドでは解消している。担当外を変更していない。

### 全δ関係を消す評価への次工程（予定名の登録）

次のBS専用予定`DeltaPDivisionWittResidueEvaluation.lean`で、元族y:σ→Aと
通常射q:A→B、全q(y_s)=0について、相対自由δ環Lの逆Witt座標射を使う。
Witt座標X_(s,n)を今回の具体解t_sの第n係数へ送る通常評価と逆座標射を合成する。
基底係数のWitt自然性と今回のWitt積方程式から、元の除算関係の全Witt係数が零となることを確認する。
既存deltaWittGhostVector_jets_zero_iffで全δ反復関係の消滅へ移し、
既存deltaDivisionIteratedRelationsLiftによってrawδ包A{φ(y_s)/p}→Bの実通常環射を構成する。
A,B,σ:Type u、Aのp正則性とA・Lのghost単射を明示し、終域のδ構造は要求しない。
この評価は任意元族を対象とする。有限生成性・Noether性は追加しない。

続くBS専用予定`DeltaPDivisionResidueMap.lean`では、一元[Unique σ]、
yのA/pでの正則性・単元δ(p)と今回までのraw p正則性の条件を明示する。
上の評価をq:A→A/(p,y)へ適用し、証明済みraw/旧ねじれ除去商同型を使って因子化する。
終域ではp=0なので既存の実p導来完備性を供給し、既存の環としてのPD完備化一意延長を使って
実DerivedDeltaDivisionCompletion D p (φ(y))→A/(p,y)を構成し、標準単位・基底射との図式を証明する。
sourceの(p,y)が正則であるこの入口と、一般の導来基底変更後のKoszul代数への写像は区別する。
一般のyがA/pで零因子である場合にraw評価が旧pねじれ除去商を経由するとは推論しない。
さらに普通のA/(p,y)への射だけから、一般の実導来Koszul代数への射を得たとはしない。
一般の導来基底変更に沿う比較・分冪包比較・CFF根付き拡大・一般B4は未完成。

## B4-6：Witt解による全δ関係消滅と任意元族のraw通常評価（2026-10-15）

`DeltaPDivisionWittResidueEvaluation.lean`で、任意元族y:σ→Aと通常射q:A→B、
全q(y_s)=0から、既存逆Witt座標射に具体的Witt除算解を代入した通常環射を構成した。
自由初期変数と係数の全Witt元の像を比較し、元のp除算関係の全Witt係数が零となることを証明した。
既存deltaWittGhostVector_jets_zero_iffによって全δ反復関係の消滅へ移し、
既存deltaDivisionIteratedRelationsLiftでrawδ包A{φ(y_s)/p}→Bの実通常環射を公開した。
自由環の評価・基底の係数射との図式と、初期除算変数の像q(δy_s)を供給した。
A,B,σ:Type u、Aのp正則性・Aと自由δ環のghost単射を明示する。
終域Bのδ構造・p正則性・標数p・完備性や、元族の有限性は不要。
12公開宣言の対象2136ジョブ、pure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
今回の全体ビルドは共有IdempotentImageTrivial.lean:23の
cochainAcyclic_iff_support_bot未解決で失敗した。ログ/tmp/bs-p-witt-eval-full.log。
担当外は変更していない。
次は登録済みDeltaPDivisionResidueMapの正則一元の旧ねじれ除去商・実H⁰への因子化を監査する。
一般の導来Koszul代数への射・CFF・一般B4は未完成。

## B4-6：正則一元p除算の実H⁰からの具体的通常剰余射（2026-10-15）

`DeltaPDivisionResidueMap.lean`で、一元[Unique σ]に対する前工程の通常評価を
既存raw/旧ねじれ除去商同型で因子化した。
Aのp正則性、yのA/p正則性、単元v=δ(p)、A・自由δ環のghost単射を明示する。
q:A→Bがp,yを消すとき、終域自身の実p導来完備性を既存の零スカラー判定で供給し、
既存の環としての実PD完備化一意延長から
DerivedDeltaDivisionCompletion D p (fun _↦φ(y))→Bを構成した。
旧ねじれ除去商の標準射・実Koszul標準単位・元の基底射との全図式を公開した。
qが全射ならこの通常剰余射も全射である。
特にB=A/(p,y)、q=標準商射の具体的な名前付き環射と全射性を供給した。
終域Bのδ構造や非零性・有限生成性は要求しない。

11公開宣言の対象3897ジョブ、pure B4監査、全体4927ジョブ成功。
標準3公理のみ、新sorry・公理・引用なし。共有既存sorry警告は別扱い。
前工程d122955の全体ビルドの共有失敗は、今回の全体ビルドでは解消している。
この全射性は特定の実H⁰からの通常剰余射であり、最終B4のperfectoid化射の全射性とは異なる。
一般の導来基底変更後のKoszul代数への射を得たとはしない。

### 実導来比較へ進む次工程の登録

次のBS専用予定`DeltaDivisionFiniteLeadingLinear.lean`で、通常mod p表示に留まらず、
実反復関係g_(s,n)=δ^n(d*X_(s,0)−a_s)の最高δ変数を整係数のまま分離する。
目標は、初期n段の具体的有限多項式b_(s,n)の存在と
  g_(s,n)=C(φ^n(d))*X_(s,n)+initialMap_n(b_(s,n))
という実際のL内の等式。n=0も含め、下位多項式には第n段の変数が現れないことを保持する。
既存のδ加法・積公式と有限δ段数制御を使う。
既存DeltaDivisionFiniteTopCoefficientはmod pの主張なので、この整係数等式の代用にしない。
新しい共通Tor・完全平坦性・導来完備化定義は作らない。

d=pならφ^n(p)=pである。この表示を、全有限段のp正則性と変数分離に接続し、
実δ関係列そのものの弱正則性・Koszul分解を検証する工程へ進む。
p正則な通常商であることだけから、原典の導来δpushoutの離散性を推論しない。
有限実Koszul比較と無限段への移行を区別し、必要な共通比較は既存APIを調べてから要求に記録する。
分冪包比較、一般の実導来比較、CFF根付き拡大、一般B4は未完成。

## B4-6：実δ反復関係の整係数での一次分離（2026-10-15）

`DeltaDivisionFiniteLeadingLinear.lean`を実装した。任意のδ環A、任意添字σ、d:A、a:σ→A、
全深さnについて、実関係δ^n(C(d)X_(s,0)−C(a_s))を
C(φ^n(d))X_(s,n)+initialMap_n(b_(s,n))と表した。
b_(s,n)はσ×Fin n上の多項式なので、第n段変数を含まない。
存在・選択された多項式・等式・一意性・有限初期環内の等式を公開した。
d=pではφ^n(p)=pによって最高係数が整係数でpと証明した。
δ加法のWitt繰上りの自然性と有限δ段数制御を使用し、mod pへの移行やp正則性は不要。

6公開宣言の対象2064ジョブ、pure B4監査、全体4927ジョブ成功。
依存は標準3公理のみ、新sorry・公理・引用なし。既存共有sorry警告は別扱い。
この等式から有限δ関係列の正則性・実導来比較・CFFを自動的には結論しない。
一般B4のperfectoid化射の全射性は未完成。

### 次工程の登録：初期関係商の後続変数分離

BS専用`DeltaDivisionFiniteStageTailQuotient.lean`で、初期n段だけに属する通常関係イデアルと、
その自由δ環への拡張の商を、初期商を係数環とする後続変数の多項式環に同定する。
既存relativeFreeFiniteVariableSplitAlgEquivとMvPolynomialの係数商同型を使う。
具体的な初期関係イデアル、元の標準商射、次の実関係の一次表示との図式を供給する。
この比較を、既存全有限段p正則性と一次関係の正則性の接続に利用する。
一般の導来基底変更・分冪包比較・CFF根付き拡大は別工程として残る。

## B4-6：有限実関係商の後続変数表示（2026-10-15）

`DeltaDivisionFiniteStageTailQuotient.lean`で任意初期イデアルJについて
L/(initialMap(J))≃(P/J)[後続変数]を構成し、初期元・後続変数・標準商射の図式を証明した。
全深さ≤Nの実δ関係を初期N+1段で生成する具体的イデアルを定義し、その拡張が
既存deltaDivisionFiniteRelationIdealに一致することを証明した。
これにより実有限関係商の後続変数表示と、次の実関係の一次式の具体的な像を公開した。
全自由環の有限関係商がp正則なら、初期有限関係商もp正則であることを証明した。

12公開宣言の対象3213ジョブとpure B4監査成功。新sorry・公理・引用なし。
通常商の表示であり、実導来δ基底変更・CFF・一般B4は未完成。

### 次工程の登録：実一元関係列の正則性

BS専用`DeltaPDivisionFiniteRelationsRegular.lean`で、正則な最高係数pを持つ一次式の
非零因子性を、前工程の実有限関係商の後続表示へ適用する。
既存全有限段p正則性の仮定（Aのp正則性、yのA/p正則性、単元δp、自由環ghost単射）を明示し、
実δ関係g_0,…,g_N自身の弱正則性と既存IsKoszulResolutionを目標にする。
前置したpを含む列だけの分解と混同せず、通常mod pの正則性だけから結論しない。
導来δpushoutとの比較はこの通常Koszul分解とは別工程とする。

この工程の全体ビルド4928ジョブも成功。共有既存sorry警告は別扱い。

## B4-6：実一元δ関係列自身の正則性とKoszul分解（2026-10-15）

`DeltaPDivisionFiniteRelationsRegular.lean`で、初期商のp正則性と前工程の後続変数表示から、
次の実関係g_(N+1)がL/(g_0,…,g_N)上の非零因子となることを証明した。
最初の関係g_0はAのp正則性だけで非零因子である。
正則一元y、単元δ(p)、自由δ環ghost単射を明示し、全Nについて
実列g_0,…,g_N（pを前置しない）の弱正則性と既存IsKoszulResolutionを公開した。
その列の生成イデアルが既存の実有限関係イデアルI_Nに一致することも証明した。
一般係数の正則一次式の議論はこのBSファイルのprivate補題として使用した。

6公開宣言の対象3807ジョブ、pure B4監査、全体4932ジョブ成功。
標準3公理のみ、新sorry・公理・外部引用なし。共有既存sorry警告は別扱い。
全有限実Koszul複体の分解は得られたが、無限δ関係と導来δpushoutの同一視やCFFは未証明。
André引用に相対的な成果は今回使用せず、一般B4の全射性は未完成。

### 次工程の登録：標準単位で正規化した有限実Koszul比較

BS専用`DeltaPDivisionFiniteKoszulComparison.lean`で、既存koszulCanonicalH0Equivと
実関係イデアルの一致を使い、H⁰K(g_0,…,g_N)≃L/I_Nを標準単位上で正規化する。
その同型により実Koszul複体から(L/I_N)[0]への準同型・擬同型を構成する。
既存koszulAugmentationはIsKoszulResolution.equivの選択を使うため、
そのままでは標準商射との両立・段間自然性を主張しない。
標準単位の図式を明示し、有限段から無限段への移行や実導来δ基底変更とは区別する。
共通層のKoszul・Tor・導来完備化定義は再利用する。

## B4-6：標準単位で正規化した実有限Koszul比較（2026-10-15）

`DeltaPDivisionFiniteKoszulComparison.lean`で、既存koszulCanonicalH0Equivにより
H⁰K(g_0,…,g_N)≃L/I_Nを構成し、元r:Lの標準H⁰単位が標準商元[r]へ写ることを証明した。
この正規化H⁰同型自体にはp正則性・y正則性・ghost単射を要求しない。
さらに実Koszul複体から(L/I_N)[0]への添加写像を作り、
そのH⁰写像が正規化同型に一致し、標準単位上で実標準商射に一致することを公開した。
既存の正則一元入力（p正則A、yのA/p正則性、単元δp、自由環ghost単射）では
その実添加写像がQuasiIsoであると証明した。
IsKoszulResolution.equivの任意選択に基づく既存添加写像を、標準商射と無根拠に同一視していない。

7公開宣言の対象3809ジョブとpure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
この比較は有限Koszulモデルと具体的通常商の間のもの。
無限δ関係の実モデル、導来δ基底変更との比較、分冪包比較、CFF根付き拡大、一般B4は未完成。

### 次工程の登録：実有限Koszul比較の段間自然性

BS専用`DeltaPDivisionFiniteKoszulTransitions.lean`で、実列の末尾へ次のδ関係を付加する
既存mappingCone.inrによる実鎖写像K_N→K_(N+1)と、既存I_N≤I_(N+1)の商射を置く。
既存koszulH0Unit_succを使い、鎖写像が標準単位を保つこと、
正規化H⁰同型が商の標準遷移射と可換であることを証明する。
有限次元・元族有限性とは別に、δ深さNの全有限段を一つの図式として揃える。
その後に、既存のfiltered-colimitとホモロジーの交換を調査し、
実鎖複体図式のcolimitとrawδ関係商の比較へ進む。
固定列の係数環の極限を扱う既存KoszulDirectedUnion等だけから、
列の長さが増える今回の比較を得たとはしない。
一般の導来δpushout・CFFへの接続は引き続き別途証明する。

この工程の全体ビルド4932ジョブも成功。共有既存sorry警告は別扱い。

## B4-6：実有限Koszul比較の段間自然性（2026-10-15）

`DeltaPDivisionFiniteKoszulTransitions.lean`で、実mappingCone.inrによる
K(g_0,…,g_N)→K(g_0,…,g_(N+1))の鎖写像を構成した。
既存koszulH0Unit_succからそのH⁰写像が標準単位を保存することを証明した。
通常商側の射は既存Ideal.Quotient.factorによるL/I_N→L/I_(N+1)を使用し、
標準商元の図式と、正規化H⁰同型が両遷移射と可換になることを証明した。
標準H⁰単位の全射性を使ったため、これらの自然性にはp正則性・y正則性・ghost単射は不要。
さらに実Koszul複体と実鎖写像からなる具体的なℕ図式を構成し、隣接射を同定した。

### 次工程の登録：実H⁰図式と通常商図式の自然同型

BS専用`DeltaPDivisionFiniteKoszulHomologyDiagram.lean`で、通常有限商を共通のL加群圏に置く
具体的な逐次図式を作り、正規化H⁰同型による自然同型を供給する。
前工程の元ごとの可換図式を使い、実Koszul図式のhomologyFunctor像と比較する。
その後に、既存filtered-colimit交換の適用条件と、通常商図式の極限がrawδ包となる
標準射付き比較を調べる。実Koszul図式の極限の正次数ホモロジー消滅・H⁰の同定を順に証明する。
列長が増える今回のモデルを、固定列のKoszul係数環極限の既存APIと混同しない。
この無限通常Koszulモデルを原典の導来δ基底変更と同一視する比較も別途必要であり、
一般B4、分冪包比較、CFF根付き拡大は未完成のまま。

本工程の7公開宣言の対象3810ジョブ、pure B4監査、全体4933ジョブ成功。
標準3公理のみ、新sorry・公理・外部引用なし。共有既存sorry警告は別扱い。

## B4-6：実H⁰図式と通常有限商図式の自然同型（2026-10-15）

`DeltaPDivisionFiniteKoszulHomologyDiagram.lean`で通常有限商の標準射をL線形化し、
共通L加群圏内の実逐次図式を構成した。
前工程の標準単位に基づく可換図式により、実Koszul図式へhomologyFunctorを施したH⁰図式と
通常有限商図式との自然同型を公開した。各成分は既存の正規化H⁰同型そのもの。
自然同型にはAのp正則性・y正則性・ghost単射は不要。
6公開宣言の対象3811ジョブ成功。新sorry・公理・引用なし。

### 次工程の登録：実逐次Koszul極限のホモロジー

BS専用`DeltaPDivisionSequentialKoszul.lean`で、具体的な実Koszul図式をℤ次数の
逐次図式の複体へ転置し、既存の完全なcolim関手とShortComplex.mapHomologyIsoを適用する。
共通SequentialComplexColimits.leanは現在ℕ次数に特化しているため、その定理をℤにそのまま
適用できたとはしない。BSの当該図式に限る転置・比較を構成し、新しい一般共通APIは作らない。
実圏論的colimitのホモロジーと各有限段のホモロジーのcolimitを比較する。
正則一元入力では有限段IsKoszulResolutionから零以外の全次数でのホモロジー消滅を導く。
H⁰は前工程の自然同型を通して通常有限商図式のcolimitと同定する。
rawδ包との標準射付き同定、原典の導来δ基底変更との比較、CFFは別工程として残る。

本工程のpure B4監査・全体4933ジョブも成功。依存は標準3公理のみ。
共有既存sorry警告は別扱い。

## B4-6：実逐次Koszul極限のホモロジー（2026-10-15）

`DeltaPDivisionSequentialKoszul.lean`で、BSの実図式をℤ次数で転置し、
既存の完全なcolim関手・ShortComplex.mapHomologyIso・評価による実colimit構成を適用した。
ModuleCatの既存AB5をAB5OfSize_of_univLEでℕ添字のサイズへ適用した。
当該の実圏論的colimitについて、各次数のホモロジーと実有限段ホモロジーのcolimitの同型を公開した。
H⁰は前工程の自然同型を通して通常有限商図式のcolimitに同定した。
正則一元入力（p正則A、yのA/p正則性、単元δp、自由環ghost単射）では
零以外の全ℤ次数のホモロジーが零であると証明した。
固定有限列の係数環極限とは別に、実際に列長が増すKoszul図式を扱っている。
7公開宣言の対象3855ジョブ成功。新sorry・公理・引用なし。
rawδ包との同定と原典の導来δ基底変更との同定は、この段階では未証明。

### 次工程の登録：通常有限商図式のrawδ包への標準極限比較

BS専用`DeltaPDivisionFiniteQuotientColimit.lean`で、各I_Nが実δ閉包Jに含まれることから
標準射L/I_N→L/J=DeltaAdjoinDivision D p (fun _↦φy)を置く。
共通L加群圏で具体的な余錐を作り、そのIsColimitを証明する。
既存J=iSup I_Nと有限商図式の標準商元の遷移式を使い、任意の加群余錐への降下を
Lからの線形写像の商によって構成する。単なる環同型の存在ではなく標準射上の図式を保つ。
次に前工程のH⁰比較へ接続し、実無限KoszulモデルのH⁰をrawδ包へ正規化する。
これにはAのp正則性・y正則性・ghost単射は不要である。
原典の導来δpushoutとの比較・分冪包比較・CFF根付き拡大・一般B4は別工程として残る。

本工程のpure B4監査と全体4936ジョブも成功。依存は標準3公理のみ。
共有既存sorry警告は別扱い。

### 次工程の登録：raw δ包への実無限Koszul添加写像

BS専用`DeltaPDivisionSequentialKoszulAugmentation.lean`で、実Koszul図式のcolimitから
rawδ包を零次数に置いた複体への具体的な添加写像を構成する。
各有限Koszul複体の正次数の項が零であることと、評価関手のcolimit保存から
実極限のX¹=0を示し、既存toSingleOfHomologyを適用する。
H⁰比較には前工程のraw δ包への同型を使い、正則一元入力では実添加写像のQuasiIsoを示す。
これは実無限Koszulモデルとraw通常商との比較であり、
原典の導来δpushoutや完備化・CFFとの比較を完了したという主張ではない。
各有限段標準単位の極限からの像をraw標準商元に同定する図式は、
既存ホモロジー・colimit比較の自然性を確認してから公開する。

## B4-6：raw δ包は実有限通常商図式の標準colimit（2026-10-15）

`DeltaPDivisionFiniteQuotientColimit.lean`で、各有限商L/I_Nから実δ閉包商L/Jへの
標準L線形射を置き、その射が標準商元を保つことを証明した。
任意の加群余錐について、有限段からの像が元r:L上で段に依らないことを示し、
J=iSup I_Nを用いてLからの線形写像を実δ閉包商で割り、具体的なIsColimitを構成した。
実圏論的colimit≃raw δ包の同型と、各有限段の標準射との可換図式を公開した。
前工程の実H⁰極限比較へ接続し、実無限KoszulモデルのH⁰をraw δ包にL線形同定した。
このcolimit比較にはp正則性・y正則性・ghost単射は不要。
7公開宣言の対象3860ジョブ成功。新sorry・公理・外部引用なし。

途中の通常ビルドは共有CochainTensor.leanのHasTensor不足と、その後の共有.olean欠落で停止した。
共有層のソース修正とオブジェクト再生成後の通常対象ビルドは成功している。
担当外の共有ファイルは編集していない。
原典の導来δpushoutやCFFとの同定は、この通常colimit比較から自動的には結論しない。

本工程のpure B4依存監査成功。依存は標準3公理のみ。
全体ビルドは次の無限Koszul添加写像の工程と合わせて実行中。

## B4-6：raw δ包への実無限Koszul添加写像（2026-10-15）

`DeltaPDivisionSequentialKoszulAugmentation.lean`で、実Koszul図式の圏論的colimitの
正次数の項が零であることを、既存の評価関手のcolimit保存と有限段の項の消滅から証明した。
特に実d⁰¹=0を供給し、既存toSingleOfHomologyと証明済み実H⁰比較によって
実無限Koszul複体→rawδ包[0]の具体的な鎖写像を構成した。
その実H⁰写像がraw比較同型に一致することを公開した。
正則一元入力（p正則A、yのA/p正則性、単元δp、自由環ghost単射）では、
この実無限添加写像がQuasiIsoであると証明した。
5公開宣言の対象3861ジョブとpure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
原典の導来δpushout・導来完備化・分冪包比較・CFFを証明したとは数えない。

### 次工程の登録：実無限比較の標準単位の正規化

BS専用`DeltaPDivisionSequentialKoszulUnit.lean`で、
各有限段K_N→実colimitのH⁰写像と、実H⁰極限比較の可換図式を証明する。
前工程の実比較はShortComplex.mapHomologyIsoから構成しているので、
同型の存在だけから標準単位保存を推論しない。
逐次図式の評価関手からcolimへの自然変換（成分は既存colimit.ι）を使い、
既存ShortComplex.homologyMap_mapNatTransと実termwise/圏論的colimit同型の標準射の式を適用する。
目標は、任意Nとr:Lについて、有限段の標準H⁰単位を実極限へ送りraw比較を施すと
rawδ包の元[r]となる等式。さらに実無限添加写像のH⁰について同じ標準単位図式を供給する。
この段も共通Tor・完備性・Koszul定義の重複は作らず、BSの具体的な図式だけを扱う。
以後、実無限通常Koszulモデルと原典の導来δ基底変更を比較し、分冪包・CFFへ接続する。
一般B4の任意perfectoid環の商のperfectoid化全射性は未完成であり、
正則一元入力の仮定を最終公開APIへ追加する変更は行っていない。

今回の全体ビルドは共有PerfectComplex/TensorShortExact.leanとKoszulOneModel.leanで失敗した。
前者はShortComplex.Splitting・cochainTensorFixedRight等、後者はsupportZeroLocus・
HasHomologySupportOn・K0WithSupport.mk等の未解決識別子を報告した。
ログは/tmp/bs-infaug-full.log。共有コードは変更していない。
raw有限商colimit比較と実無限Koszul添加写像の対象ビルド・pure B4監査は成功しており、
全体ビルド成功とは区別する。前工程の全体4936ジョブ成功は、今回の共有変更前の記録である。

### 次工程の登録：導来基底変更で現れる有限評価関係との比較

BS専用`DeltaDivisionFiniteEvaluationRelations.lean`で、任意δ環D、任意元族a_sとdについて、
u_s=C(d)X_(s,0)、v_s=C(a_s)と置いたときの二つの実有限関係イデアルを比較する。
既存の関係はg_(s,n)=δ^n(u_s−v_s)、自由δ射の座標評価から現れる関係は
h_(s,n)=δ^n(u_s)−δ^n(v_s)であり、これらを定義上同一視しない。
目標は、全深さ≤Nで生成した両通常イデアルが全Nで一致するという証明。
δ加法の繰上りと、有限spanのδ像が次段spanへ入ることを用いる。
p正則性・ghost単射・完備性はこの純代数的なイデアル比較には要求しない。
この比較を、自由δ射の座標関係で計算する実基底変更Koszulモデルへの入口とする。
イデアル一致だけからKoszul複体の擬同型や導来δpushoutの同一視は主張せず、
評価関係列自身の正則性・標準評価写像・実導来テンソル比較を順に証明する。
著者公開版Cor 2.44（p.27）の導来pushoutを通常商へ無条件に置換しない。

## B4-6：実無限Koszul比較の標準単位の正規化（2026-10-15）

`DeltaPDivisionSequentialKoszulUnit.lean`で、評価関手からcolimへの自然変換と
既存ShortComplex.homologyMap_mapNatTransから、実ホモロジー極限比較が
各有限段の実圏論的標準射を保つことを全ℤ次数で証明した。
H⁰の通常有限商図式との比較、rawδ包との比較まで可換図式を接続した。
任意Nとr:Lについて、有限段の標準H⁰単位を実極限へ送りraw比較を施すと[r]となる。
実無限添加写像の実H⁰も同じ標準単位の式を満たすと証明した。
p正則性・y正則性・ghost単射・完備性は、この正規化の等式には不要。
5公開定理の対象3862ジョブ・pure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
今回の全体ビルドは共有IntersectionMultiplicity/AdamsVanishingThree.leanで、
共有KTheory/Adams/TensorCubeLowMixedSections.oleanの欠落により失敗した。
ログ/tmp/bs-infunit-full.log。担当外の共有ファイルは変更していない。
対象・依存監査成功と全体ビルド成功を区別する。
原典の導来δ基底変更との比較、分冪包比較、CFF根付き拡大、一般B4は未完成。

### 次工程の登録：自由δ射の具体的な評価源と核の像

BS専用`DeltaDivisionEvaluationSource.lean`で、実源P=A{x_s}と実終域L=A{z_s}、
δ射α:P→L（x_s↦d z_s）、β:P→A（x_s↦a_s）を既存relativeFreeDeltaEvalで構成する。
α(X_(s,n))=δ_L^n(C(d)X_(s,0))、β(X_(s,n))=δ_A^n(a_s)と係数上の標準図式を公開する。
βの核が座標グラフ関係X_(s,n)−C(δ^n(a_s))で生成されることを証明する。
前工程の有限評価関係イデアル比較を使い、α(ker β)の拡張イデアルが
実rawδ除算包の定義δ閉包に一致することを証明する。
さらにraw標準射q:L→L/Jと基底射j:A→L/Jに関しq∘α=j∘βを具体的に示す。
通常の基底変更の環・写像を確定する工程であり、Tor消滅や導来基底変更の同定は別工程。
p正則性・ghost単射・完備性をこの通常核比較へ追加しない。

## B4-6：有限評価関係と実反復差関係のイデアル一致（2026-10-15）

`DeltaDivisionFiniteEvaluationRelations.lean`で、全深さ≤Nについて
δ^n(u_s−v_s)とδ^n(u_s)−δ^n(v_s)が生成する通常イデアルの一致を証明した。
δ加法のWitt繰上りを商へ送り、δ(x)−δ(y)−δ(x−y)が(x−y)を含むイデアルに入ること、
有限生成spanのδ像が次段イデアルに入ることを用いた。
実自由δ環のu_s=C(d)X_(s,0)、v_s=C(a_s)へ適用し、既存deltaDivisionFiniteRelationIdealと同定した。
評価関係の定数側をC(δ_A^n(a_s))と表し、各評価関係の有限イデアルへの所属と
実raw δ除算包の標準商射での消滅を公開した。
p正則性・ghost単射・完備性や添字有限性を要求しない。
6公開宣言の対象2061ジョブ・pure B4監査成功。標準3公理のみ、新sorry・公理・引用なし。
直前の全体ビルドは共有AdamsVanishingThreeの共有.olean欠落で失敗した記録のまま。
この純代数的なイデアル一致だけからKoszul複体や導来pushoutの同一視を結論しない。

## B4-6：具体的な自由δ射・評価核とraw δ包の通常pushout（2026-10-15）

`DeltaDivisionEvaluationSource.lean`で、P=A{x_s}、L=A{z_s}と解釈する実相対自由環に対し、
α:P→L（x_s↦d z_s）とβ:P→A（x_s↦a_s）を既存relativeFreeDeltaEvalで置いた。
両射のδ構造保存・係数上の式・全δ座標の式を公開した。
βの核はX_(s,n)−C(δ_A^n(a_s))のspanであることを、商での変数の値と多項式射の一意性から証明した。
αで各グラフ関係を写すと前工程の実評価関係になること、
α(ker β)の拡張イデアルが既存raw δ包の実定義δ閉包に一致することを証明した。
raw標準商射qと基底射jに関しq∘α=j∘βを示した。
さらに任意の可換環Bと整合する実環射f:A→B、g:L→Bから、
raw δ包→Bへの一意な環射が存在して両標準射を保つと証明した。
終域Bのδ構造・完備性・p正則性を要求しない、通常の環としてのpushout普遍性である。
対象2062ジョブ成功。新sorry・公理・外部引用なし。
通常pushoutの普遍性から、原典Cor 2.44の導来pushoutの同一視はまだ推論しない。

### 次工程の登録：源評価核の有限グラフKoszul分解

BS専用`DeltaDivisionSourceGraphKoszul.lean`で、源P上のグラフ関係
X_(s,n)−C(δ_A^n(a_s))の、任意の重複しない有限座標族について弱正則性と
既存IsKoszulResolutionを証明する。
既存の任意先行添字集合の多項式商分離（deltaRootSubsetQuotientEquivの指数1の場合）と
モニック一次式の非零因子性を使う。既存の根関係の正則性定理はFact p.Primeを要求するため、
それをp=1へ無条件に適用したとはしない。指数1のモニック性は当該BS証明内で供給する。
この源側の正則性にはAのp正則性・ghost単射・完備性・元族有限性を要求しない。
特に一元の全有限深さを取り、源評価射βへ向かう実Koszul分解の各段の入力を揃える。
次にαに沿う実基底変更で出る評価関係Koszulモデルへ接続し、
既存の反復差関係の実分解と比較する。通常商の一致だけをTor消滅や導来比較と取り違えない。
一般B4の全射性、分冪包比較、CFF根付き拡大は未完成。

本工程の13公開宣言のpure B4依存監査成功。依存は標準3公理のみ。
全体ビルドは共有TensorShuffleでCochainTensorLinear.oleanの欠落を報告したが、
他の共有利用先の再ビルドがなお実行中であり、この工程のコミット時点では終端未確認。
対象ビルド成功と全体成功は区別する。

## B4-6：源評価核の有限グラフKoszul分解（2026-10-15）

`DeltaDivisionSourceGraphKoszul.lean`で、源グラフ関係
X_(s,n)−C(δ_A^n(a_s))の任意の重複しない有限座標族について弱正則性とIsKoszulResolutionを証明した。
任意の先行添字部分集合の商表示は既存deltaRootSubsetQuotientEquiv(p:=1)を使い、
残りの関係の非零因子性はモニック一次式X−C(b)で示した。
Fact 1.Primeを仮定したり、既存の素数冪根正則性を指数1へ不正に適用したりしていない。
αに沿うグラフ関係の通常像が、実終域の評価関係になることも公開した。
Aのp正則性・ghost単射・完備性・添字集合の有限性は不要。
4公開宣言の対象3518ジョブ成功。新sorry・公理・外部引用なし。

### 次工程の登録：実p除算評価関係列の正則性

BS専用`DeltaPDivisionFiniteEvaluationRegular.lean`で、一元[Unique σ]、d=p、a_s=φ(y)の
実評価関係h_n=δ_L^n(C(p)X_0)−C(δ_A^n(φ(y)))の全有限列の弱正則性・実Koszul分解を証明する。
既存の反復差関係g_nの正則性と、全有限prefixのイデアル一致を使う。
前段商では(g_n)=(h_n)なので、g_nが非零因子ならh_nも非零因子となることを確認する。
単なる全最終イデアルの一致から関係列の正則性を推論しない。
Aのp正則性・yのA/p正則性・単元δp・自由δ環ghost単射は、既存実g列の中間仮定として明示する。
その後、源グラフKoszul分解をαに沿って基底変更した評価関係Koszul複体へ
既存torAlgKoszulEquivを適用し、具体的な有限源商に対する正次数Tor消滅を証明する。
全源評価環Aへの無限段移行と、原典の導来δpushout比較は別途残る。
一般B4、分冪包比較、CFF根付き拡大は未完成。

源グラフKoszul分解の4公開宣言についてpure B4監査も成功。標準3公理のみ。
全体ビルドは共有TensorShuffleの.olean欠落を報告後、残りの利用先をなおビルド中。

### 次工程の登録：実自由δ射に沿う有限源商のTor消滅

BS専用`DeltaPDivisionSourceFiniteTor.lean`で、P=A{x}→L=A{z}、x↦p zの実環射αと
源の有限グラフ関係X_n−C(δ_A^n(φ(y)))（0≤n≤N）の実商Q_Nを使う。
源グラフ関係の実Koszul分解と既存torAlgKoszulIsoにより、
TorAlg α i Q_Nを、終域Lの実評価関係Koszulホモロジーに同定する。
正則一元入力の仮定を明示し、i>0のTor消滅を証明する。
Q_Nと全源評価環Aを同一視しない。Aへの移行にはN→∞のTor/実導来テンソル比較が別途必要。
これを実自由δpushoutの導来基底変更比較へ接続するための有限段の具体的成果とする。

## B4-6：実有限p除算評価関係列の正則性（2026-10-15）

`DeltaPDivisionFiniteEvaluationRegular.lean`で、各有限prefixの実評価関係イデアルの式を公開し、
一元の全prefixの生成イデアルが既存I_Nに一致することを証明した。
前段商において次の実反復差関係g_(N+1)が評価関係h_(N+1)の倍数となることを示し、
g_(N+1)の非零因子性をh_(N+1)へ移した。
単なる最終イデアルの一致を正則列の一致と見なしていない。
Aのp正則性、yのA/p正則性、単元δp、自由δ環ghost単射の既存仮定の下で、
実評価関係h_0,…,h_N自身の弱正則性とIsKoszulResolutionを証明した。
5公開宣言の対象3817ジョブ成功。新sorry・公理・外部引用なし。
この分解は、具体的なαによる源グラフKoszul分解の実基底変更とのTor比較に用いる。
全源Aへの無限段移行・一般B4・CFF根付き拡大は未完成。

実評価関係列の5公開宣言のpure B4監査も成功。標準3公理のみ。
全体ビルドは共有TensorShuffleの.olean欠落を報告した実行の終端待ち。

## B4-6：実自由δ射に沿う有限源商の正次数Tor消滅（2026-10-15）

`DeltaPDivisionSourceFiniteTor.lean`で、実P=A{x}、L=A{z}とα:x↦p zに対し、
源評価核の有限グラフ列z_0,…,z_Nと、実商Q_N=P/(z_0,…,z_N)を定義した。
源グラフの既存実Koszul分解を供給し、既存torAlgKoszulIsoを実αに適用して
TorAlg α i Q_Nと終域の実評価関係Koszulホモロジーの同型を構成した。
Aのp正則性・yのA/p正則性・単元δp・自由δ環ghost単射の下で、全N、i≥1のTor消滅を証明した。
5公開宣言の対象3818ジョブ成功。新sorry・公理・外部引用なし。
Q_Nを全源評価環Aと同一視せず、有限段Torの消滅を全Tor消滅とは数えていない。

### 共通基盤への要求 G7：TorAlgと加群の逐次colimit（2026-10-15送信済み）

- 対象：任意u、可換環R,C:Type u、実環射φ:R→+*C、F:ℕ⥤ModuleCat.{u} R、i:ℕ。
- 必要な結論：`PreservesColimit F ((ModuleCat.extendScalars φ).leftDerived i)`。
  同値な公開APIとして、実標準比較
  `((ModuleCat.extendScalars φ).leftDerived i).obj (colimit F) ≅
    colimit (F ⋙ (ModuleCat.extendScalars φ).leftDerived i)`と、各nの標準射上の式を供給する形でもよい。
  Fの射の単射性、有限生成性、Noether性、各段の平坦性、p完備性は追加しない。
- 利用工程：B4-6。実自由δ射α:P→Lに対する有限グラフ商Q_Nの正次数Tor消滅を、
  全源評価環Aへの段階的極限に沿って移す工程。
- 既存APIの不足：既存torAlgKoszulIsoは有限源商Q_NのTorを計算できるが、
  その値のN→∞移行は与えない。共通SequentialComplexColimitsは実複体のホモロジーと
  colimitの交換を持つが、任意加群図式に対する実leftDerivedのcolimit比較ではない。
  MathlibのAbelian/LeftDerivedとリポジトリのTor周辺に対応APIは検索時点で見つからなかった。
- 待つ工程：有限源商から全源評価環への正次数Tor消滅の移送。
- 独立作業：βの核とraw通常pushout、分母1のraw包≃評価環、源有限商の具体的表示、
  既存実Koszulモデルの標準図式、原典分冪比較の具体化は続けられる。
- 共通Tor基盤の担当領域のため、同等の一般Tor/colimit定義・定理をBS内に重複構築しない。
  他チャットへの送信は行っていない。

### 次工程の登録：分母1のraw δ包と実源評価環

BS専用`DeltaDivisionUnitDenominator.lean`で、δ自由射α_1:x_s↦1·z_sが実恒等射となること、
βが係数射Cを切断として全射となることを示し、raw δ包DeltaAdjoinDivision D 1 a≃Aを構成する。
前工程の核の像の式を使って実定義δ閉包をker βと同定し、既存の商核同型を適用する。
標準商射・基底射C・生成元・δ構造との可換図式を供給する。
この通常源評価環の同定はG7を待たず進め、導来テンソルの離散性とは分ける。

有限源商Tor工程の5公開宣言のpure B4監査も成功。標準3公理のみ。
全体ビルドは共有TensorShuffleの.olean欠落を報告後、残りの共有利用先をなおビルド中。

## B4-6：分母1の実raw δ包と源評価環（2026-10-15）

`DeltaDivisionUnitDenominator.lean`で、βの全射性を元の係数射の切断から供給し、
α_1:x_s↦1·z_sが実自由δ環の恒等射であることを示した。
既存の核の像の式から分母1の実定義δ閉包=ker βを証明し、
既存quotientKerEquivOfSurjectiveによりDeltaAdjoinDivision D 1 a≃+*Aを構成した。
標準商射の式、基底射との合成=恒等射、添加変数の像、逆射=基底標準射、δ構造保存を公開した。
Aのp正則性・ghost単射・完備性・添字有限性は不要。
9公開宣言の対象2063ジョブ成功。新sorry・公理・外部引用なし。

### 次工程の登録：源有限グラフ商の逐次colimitとβ

BS専用`DeltaDivisionSourceFiniteColimit.lean`で、一元の既存有限グラフ商Q_Nを
P加群として標準商射で繋ぐ実図式を作る。
終域AのP加群構造は具体的なβ:P→AのtoAlgebraから明示し、
βにより各Q_N→Aの標準評価射を置く。
分母1の有限評価関係が源グラフ関係となる式、有限評価イデアルの一致、
実δ閉包=iSup有限関係、分母1δ閉包=ker βを使い、ker β=iSup有限グラフイデアルを示す。
MathlibのModuleCatのfiltered-colimit構成を利用して、各元の有限段表示と
核の元がある有限段で零になることから、標準評価余錐がIsColimitとなることを証明する。
一般のTor/colimit定理をBSで重複構築せず、G7の受領前もこの具体的源評価の比較を進める。
G7受領後はこの実標準colimitと有限源商のTor消滅を接続できる。
全源評価環AへのTor移送と原典の導来δpushout比較・CFF・一般B4はまだ未完成。

### 今回の全体ビルドの終端記録

/tmp/bs-evalsource-full.logの実行は終端を確認し、全体ビルドは失敗した。
失敗ターゲットは共有PerfectComplex/TensorShuffle、CubicActionTensorEigen、
KTheory/Adams/KoszulOneBasis、PerfectComplex/CubicActionClass、KTheory/Adams/WeightDefectLift。
CochainTensorLinear、IdempotentDecomposition、InvolutionDecomposition、CubicActionProjector等の
共有.olean欠落を報告した。担当外のファイルは変更していない。
各BS対象ビルド・pure B4監査の成功と、全体ビルド成功を区別する。

分母1のraw δ包比較の9公開宣言についてpure B4監査も成功。依存は標準3公理のみ。
全体ビルドは上記の共有失敗の終端記録と区別する。

### 次工程の登録：G7を明示した全源評価環へのTor移送

BS専用`DeltaPDivisionSourceColimitTor.lean`で、具体的な源有限商図式F、α:P→L、
βで作用するAについて、標準Mathlibクラス
`PreservesColimit F ((ModuleCat.extendScalars α).leftDerived (i+1))`
を明示的な入力とした全源評価環Aの正次数Tor消滅を証明する。
証明済みFの標準colimit≃Aを実leftDerivedへ写し、既存preservesColimitIsoで
各有限源商のTorのcolimitへ移して消滅を示す。
これはG7の交換入力に相対的な接続定理であり、G7受領や無条件Tor消滅としては数えない。
新しい公理・引用・Tor定義を追加せず、共通APIが揃ったとき適用箇所が正確に確定する形にする。
G7を待つのはこの交換入力の解消だけであり、通常テンソル積とrawδ包の標準比較などは独立に進める。

## B4-6：源有限グラフ商の標準colimitは実評価環A（2026-10-15）

`DeltaDivisionSourceFiniteColimit.lean`で、源有限グラフイデアルを分母1の既存有限δ関係イデアルに同定し、
ker β=iSup有限グラフイデアルとその単調性を証明した。
β.toAlgebraによりAの具体的なP代数構造を明示し、実商Q_Nと標準線形商射の逐次図式を構成した。
各Q_N→Aのβ評価射からなる標準余錐について、任意余錐の段に依らない源環上の線形写像を
既存Submodule.liftQとLinearMap.quotKerEquivOfSurjectiveで降下し、IsColimitを証明した。
当初の具体的filtered-colimit代表元の計算に代え、既存の商核同型と余錐の普遍性を直接使った。
一般のTor/colimit基盤や新しいcolimit定義を重複構築していない。
実圏論的colimit≃Aの同型と、各有限段の標準射上の式も公開した。
p正則性・y正則性・ghost単射・完備性は不要。

14公開宣言の対象3820ジョブ・pure B4監査・全体4968ジョブ成功。
新sorry・公理・外部引用なし。pure監査の依存は標準3公理のみ。
共有の既存Inputs/SerrePositivityのsorry警告は別扱い。
前回の共有.olean欠落による全体失敗は、今回の全体ビルドでは再現しなかった。
全源AへのTor消滅の無条件移送はまだG7を待つ。
一般B4、原典の導来δpushout比較、分冪包比較、CFF根付き拡大は未完成。

### 次工程の登録：実通常テンソル積とraw δ除算包

BS専用`DeltaPDivisionSourceTensor.lean`で、[Unique σ]、a_s=φ(y)、
P=A{x}、L=A{z}、α:x↦p z、β:x↦φ(y)の既存具体射を使い、
βとαで作用させた通常テンソル積A⊗[P]Lとraw δ除算包の環同型を構成する。
βの代数構造は既存deltaDivisionSourceEvalAlgebraを使う。
αに沿うLの源P代数構造と、j∘βで与えるraw包の源P代数構造を明示する。
raw標準商射qと基底射jのq∘α=j∘β、および既存の通常pushout普遍性を使い、
テンソル両因子の包含上で標準写像を保つ比較を供給する。
源Pと終域Lの underlying 多項式環が定義上同じ型なので、
αで定めた非標準Algebra P Lを、源の恒等Algebra P Pと混同しない。
この通常テンソル比較はG7に依存せず進める。
通常テンソル積と実導来テンソルの比較・その離散性や、原典の導来δpushoutとの同一視は別途必要。

## B4-6：G7の交換入力に相対的な全源評価環へのTor移送（2026-10-15）

`DeltaPDivisionSourceColimitTor.lean`で、具体的な源有限商図式Fとα:P→Lに対し、
`PreservesColimit F ((ModuleCat.extendScalars α).leftDerived (i+1))`を明示的に受け取ると、
βで作用する実評価環AのTorAlg α (i+1) Aが零となることを証明した。
実標準colimit≃AをleftDerivedへ写し、既存preservesColimitIsoと有限源商のTor消滅を使った。
共通のTor/colimit定理や新しい公理を追加していない。

対象3821ジョブ・pure B4監査成功。依存は標準3公理のみ。
この成果はG7入力に相対的であり、G7の受領・証明済みや無条件全源Tor消滅とは数えない。
直前の全体4968ジョブは成功している。一般B4とCFFは未完成。

### 次工程の登録：実通常テンソルのp正則性と旧ねじれ商への標準比較

BS専用`DeltaPDivisionSourceTensorRegular.lean`で、一元[Unique σ]の実通常テンソル積
A⊗[P]Lについて、既存raw包のp正則性を前工程の標準環同型に沿って移す。
Aのp正則性・yのA/p正則性・単元δp・自由δ環ghost単射を明示する。
既存deltaPDivisionRawTorsionEquivと合成し、実通常テンソルから
既存DeltaDivisionTorsionQuotientへの具体的な環同型を作り、純テンソルと元の基底射の像を証明する。
これを実PDCompletionH0の入力比較に利用する。通常テンソルのp正則性を全源Tor消滅やCFFと
混同せず、G7や原典の導来δpushoutとの比較を解消したとは数えない。

## B4-6：実通常テンソル積とraw δ包の標準環同型（2026-10-15）

`DeltaPDivisionSourceTensor.lean`で、βで作用するAとα:x↦p zで作用するLの
通常テンソル積A⊗[P]Lと、既存raw δ除算包の環同型を構成した。
源Pと終域Lのunderlying型が同じでも、非標準Algebra P Lと対応するModuleを明示している。
raw包の源P作用はj∘βで与え、商射qのP代数射としての両立はq∘α=j∘βを使った。
既存TensorProduct.liftとraw包の通常pushout普遍性から両方向の実環射を作り、
両因子・raw標準商射上で逆写像となることを証明した。
純テンソルa⊗bの像はj(a)q(b)、逆射のraw標準商元[q(b)]の像は1⊗bとなる。
任意σ:Type u（元族はfun _↦φ(y)）を許し、Unique σ・p正則性・完備性・G7は不要。

13公開宣言の対象3821ジョブ成功。新規13宣言だけを読み込むpure監査も成功し、
依存は標準3公理のみ。新sorry・公理・外部引用なし。
B4全体監査は共有LocalizationTowerComparison、PerfectPrismQuotientPerfectoidization、
BoundedAboveTensorModelsの.olean欠落で一時停止した記録がある。
全体ビルド・共有依存の再生成は同じ実行を継続中であり、新規宣言の監査成功と区別する。
通常テンソルの同型を、実導来テンソルの離散性・原典の導来δpushout比較・CFFと見なさない。

### 次工程の登録：実通常テンソル入力から実導来完備化H⁰への比較

BS専用`DeltaPDivisionSourceTensorCompletion.lean`で、正則一元入力の仮定の下、
R=A⊗[P]Lと既存旧ねじれ商Uの実標準環同型を用い、
実PDCompletionH0 R p (p:R)と既存DerivedDeltaDivisionCompletion D p (fun _↦φ(y))の
環同型を、標準単位と基底Aの射の図式付きで構成する。
既存existsUnique_pdCompletionRingHomと各実H⁰の自己導来完備性を使って両方向を延長し、
一意性で逆写像を示す。U側の分母はdeltaDivisionTorsionMap D p a pであることを保持し、
map_natCastの等式だけで対応する完備性入力を移す。
古典的完備化への無条件置換や、PDCompletionの新しい定義は行わない。
これは同型な通常入力環の実導来完備化H⁰比較であり、原典の導来δpushoutやG7の解消ではない。
G7待ちの全源Tor移送だけを保留し、この標準入力比較は独立に進める。

## B4-6：実通常テンソルのp正則性と旧ねじれ商への標準比較（検証中、2026-10-15）

`DeltaPDivisionSourceTensorRegular.lean`で、既存raw包のp正則性を実通常テンソルの標準環同型に沿って移し、
既存deltaPDivisionRawTorsionEquivと合成して実通常テンソル≃旧ねじれ除去商を構成した。
純テンソルの式と、元のAからの基底標準射を保つ式も実装した。
Aのp正則性・yのA/p正則性・単元δp・自由δ環ghost単射を明示する。
G7、p完備性や新しいTor・完備化定義は用いない。

直接Lean型検査と通常対象3833ジョブは成功した。
ただし、その後の監査は共有BoundedAboveTensorFunctor、BoundedAboveDerivedAssociator等の
.olean再生成と競合して停止したため、この段階では4宣言の依存監査完了とは数えていない。
通常対象ビルドと新規4宣言の監査を連続する同じ実行で再確認中。
全体ビルド/tmp/bs-sourcetensor-full.logは終端を確認し、共有KoszulCubeCoordinatesで
共有PerfectComplex/TensorSupport.oleanの欠落により失敗した。
この記録は直前の全体4968ジョブ成功と区別する。共有ファイルは変更していない。

再検証の連続実行は終端失敗を確認した。共有BoundedAboveDerivedAssociator.lean:25で
cochainTensor_projective_Xが未解決であり、24行のProjectiveゴールが残った。
ログ/tmp/bs-sourcetensorregular-build.log。したがって、新規4宣言の監査は未完了として保持する。
DeltaPDivisionSourceTensorRegular.leanと対応するB4監査の変更は、この時点ではコミットしない。
次回の検証は同じ共有依存の状態を確認してから行い、タイムアウトを理由に既存実行を再起動しない。
現在の対象ビルド実行・監査実行・全体ビルド実行はいずれも終端を確認済み。
G7を待つ工程と、この一時的な共有ビルド不整合による検証待ちは区別する。
実通常入力のH⁰完備化比較はG7から独立しており、依存の確認後に進める。

## B4-6：保留した通常テンソル正則性の再検証（2026-10-15）

現在の共有依存でDeltaPDivisionSourceTensorRegularの対象3774ジョブと
新規4宣言のpure依存監査を連続実行し、両方の成功を確認した。
依存は標準3公理のみ。前回の共有BoundedAboveDerivedAssociatorの失敗は今回再現しなかった。
通常テンソルのp正則性、旧ねじれ商との環同型、純テンソルの標準像、基底標準射の式を
この4宣言の証明済み成果として確定する。G7には依存しない。
B4全体監査と全体ビルドは、続く実完備化H⁰比較の工程と合わせて再実行している。

保留した通常テンソル正則性を含むB4全体pure監査も今回は成功した。
新規4宣言・既存監査対象とも新sorry依存はなく、標準3公理のみ。
全体ビルドは別途同じ実行を継続している。

### 次工程の登録：実通常テンソルと実完備化比較のδ構造の両立

BS専用`DeltaPDivisionSourceTensorDelta.lean`で、実通常テンソルの既存raw比較同型に沿って、
raw包のδ切断をW₂の既存写像で引き戻す具体的δ構造を構成する。
既存DeltaStructureとwittTwoMapを使用し、新しいδ環の概念は定義しない。
比較同型の両方向がδ射であること、通常テンソルの両因子の標準包含がδ射であることを示す。

続くBS専用`DeltaPDivisionSourceTensorCompletionDelta.lean`で、実通常テンソルのδ構造に
既存deltaPDCompletionStructureを適用し、前工程の実完備化H⁰比較がδ構造を保つことを証明する。
既存pdCompletionRingHom_isDeltaHomを標準単位の式へ適用し、同型の存在だけからδ両立を推論しない。
通常テンソルのδ構造にはG7・正則性は不要。旧ねじれ商と実H⁰の比較では既存の正則一元入力を明示する。
このδ両立はG7や原典の導来δpushout比較・CFFを解消したという主張ではない。

## B4-6：実通常テンソル入力と既存候補の実導来完備化H⁰比較（2026-10-15）

`DeltaPDivisionSourceTensorCompletion.lean`で、R=A⊗[P]Lと既存旧ねじれ商Uの標準環同型を使い、
実PDCompletionH0 R p (p:R)≃+*DerivedDeltaDivisionCompletion D p (fun _↦φ(y))を構成した。
U側の実分母deltaDivisionTorsionMap D p a pを保持し、map_natCastだけで完備性入力を比較した。
既存existsUnique_pdCompletionRingHomにより両方向を延長し、実完備化普遍性の一意性で逆写像を示した。
標準単位を保つ比較同型の存在・一意性、元ごとの単位の式、元のAの標準射の式、逆射の単位の式を公開した。
Aのp正則性・yのA/p正則性・単元δp・自由δ環ghost単射を、通常入力の標準同型の仮定として明示する。
古典的完備化へ置換せず、新しい完備化の定義やG7入力は用いていない。

6公開宣言の対象3869ジョブ・B4全体pure監査成功。依存は標準3公理のみ。
新sorry・公理・外部引用なし。
全体ビルド/tmp/bs-tensorcompletion-full.logは共有KTheoryのKoszulShiftTwoClass、
KoszulSquareCoordinates、CubicUnitNormalizationで失敗した。
前者はshiftされたKoszulのクラスの未解決ゴール、後者側は型の合わないmappingCone等の式を報告した。
共有ファイルは変更していない。対象・監査成功と全体ビルド成功は区別する。
原典の導来δpushout比較・G7・分冪包比較・CFF・一般B4は未完成。

## B4-6：通常テンソルのδ構造と一意性（2026-10-15）

`DeltaPDivisionSourceTensorDelta.lean`で、raw包のδ切断を標準同型とW₂写像で引き戻した。
標準同型の両方向、両因子の包含がδ射であることを証明した。
さらに、両因子の包含をδ射にするδ構造の一意性を、W₂への環射のテンソル普遍性で示した。
任意の変数型σに対する構成であり、正則性・完備性・G7は仮定しない。
6公開宣言の対象3770ジョブとB4全体pure依存監査が成功。標準3公理のみ。
原典の導来δpushout比較やCFFを結論するものではない。

## B4-6：実通常テンソルの実完備化H⁰比較のδ両立（2026-10-15）

`DeltaPDivisionSourceTensorCompletionDelta.lean`で、通常テンソルδ構造の実H⁰への既存延長を用い、
元の基底からの標準射がδ射であることを証明した。これらは任意σで正則性を要求しない。
正則一元入力の比較では、通常テンソル≃旧ねじれ商の両方向がδ射であることを供給し、
pdCompletionRingHom_isDeltaHomと標準単位の比較式により実H⁰比較の両方向のδ両立を証明した。
既存の完備化δ構造と両立しており、完成した環同型に沿って別のδ構造を移しただけではない。
5公開宣言の対象3871ジョブとB4全体pure監査が成功。標準3公理のみ。
正則一元入力の仮定を保ち、G7や一般導来δpushout・分冪包比較・CFFの解消とは数えない。

### 次工程の登録：Lemma 2.35の反復p除算

BS専用`DeltaDividedPowerStep.lean`を追加する。既存DeltaResidueArithmeticを使い、
任意δ環、x,z∈A、x^p=pzからp∣z^pを証明する。
pを消す通常商射の下でδ(x^p)=0、δ(p)=1、δ(pz)=z^pを比較する。
これを反復し、p c_(n+1)=c_n^p、c_0=x、c_1=zの具体的な列を構成し、
p^e(n)c_n=x^(p^n)、e(0)=0、e(n+1)=p e(n)+1を示す。
p正則性・p局所性・G7はこの計算に要求しない。p正則なら最初のxに対する列の一意性を示す。
これは著者版Lemma 2.35のp典型分母に向かう代数計算であり、n!分母全体や分冪構造、
原典Cor.2.39の分冪包同定、導来pushout比較、CFFを結論するものではない。

## B4-6：δ環内の反復p除算（2026-10-15）

`DeltaDividedPowerStep.lean`で、x^p=pzならp∣z^pを一般δ環で証明した。
δを剰余環へ降ろさず、源でのδ計算を通常商射で比較する。
指定したx,zを初めの2項とする全反復除算列の存在、p冪分母を払った各項の式、
p正則な場合の列の一意性も公開した。存在と分母計算にはp正則性・p局所性・G7を要求しない。
5公開宣言の対象2065ジョブとB4全体pure監査が成功。標準3公理のみ。
階乗分母全体・分冪構造・分冪包同定・CFF・一般B4はまだ結論しない。

### 次工程の登録：Lemma 2.35の階乗分母の可除性

BS専用`DeltaFactorialDivision.lean`で、前工程のp除算閉性とMathlibの
padicValNat_factorial_mul・padicValNat_mul_div_factorialを使い、
p∣x^pから全nについてp^val_p(n!)∣x^nを示す。
n=p(n/p)+(n%p)とし、x^p=pzとzのp除算可能性へ帰納する。
さらに非p倍の自然数が単元であるというp局所性の正確な仮定の下で、n!∣x^nを示す。
p正則性を課さない代数的可除性として公開し、局所化内の分冪包同定や分冪公理とは分ける。
G7を使わず、既存の自然数p進付値APIを再利用する。

### 次工程の登録：具体的raw φ(y)/p包での全階乗分母

BS専用`DeltaPDivisionFactorial.lean`に、元族y:σ→Aに対するrawδ包B=A{φ(y_s)/p}の
具体的な元j(y_s)とv_s−j(δ(y_s))を渡す。初期p除算関係を証明し、
非p倍の自然数のAでの単元性を明示して、全nのn!∣j(y_s)^nを供給する。
具体的に選んだ分母付き元と、階乗を払った式、0・1の正規化を公開する。
任意σでpねじれを許し、分冪構造・分冪包同定とは区別する。

## B4-6：Lemma 2.35の全階乗分母の可除性（2026-10-15）

`DeltaFactorialDivision.lean`で、任意δ環のp∣x^pから全nのp^val_p(n!)∣x^nを証明した。
強帰納法でn=p(n/p)+(n%p)と分解し、x^p=pz、p∣z^pへ帰着した。
Mathlibの既存Legendre型の階乗付値公式を使い、新しい付値・Tor・完備化の定義は作っていない。
非p倍の自然数が単元であるというp局所性を明示し、全nのn!∣x^nまで証明した。
p正則性は両定理に不要。零環・pねじれを許す。
2公開宣言の対象2067ジョブとB4全体pure監査が成功。標準3公理のみ。
分母を払う可除性の結論であり、分冪構造の公理や分冪包の普遍性・導来比較・CFFはまだ未証明。

## B4-6：具体的raw包の全階乗分母（2026-10-15）

`DeltaPDivisionFactorial.lean`で、任意元族y:σ→Aのraw包B=A{φ(y_s)/p}を扱い、
j(y_s)^p=p(v_s−j(δ(y_s)))という実際の初期除算関係を証明した。
非p倍の自然数がAの単元である仮定を標準基底射でBへ移し、全nのn!∣j(y_s)^nを示した。
選んだ具体的元、n!を払った式、0・1での正規化を公開した。
任意σ・一般pねじれを許し、正則性・G7・既存André引用は用いない。
6公開宣言の対象2073ジョブとB4全体pure監査が成功。標準3公理のみ。
全体ビルド/tmp/bs-factorialdivision-full.logは同じ実行を継続している。
分冪構造の公理・分冪包の普遍性・導来pushout比較・CFF・一般B4は未完成。

### 次工程の登録：分冪分母を閉じ込める具体的イデアル

BS専用`DeltaDividedPowerIdeal.lean`で、I={x∈A | p∣x^p}を、
既存Frobenius liftによる(p)の逆像として定義し、集合表示との一致を証明する。
前工程の付値帰納法を強め、n>0の階乗分母をI内に選べることを示す。
これを既存Mathlib DividedPowers.ofInjectiveへ渡すための閉性入力にする。
p正則性は閉性には要求しない。分冪構造自体・分冪包普遍性はこの段階では未確定。

## B4-6：階乗分母を閉じ込める具体的イデアル（2026-10-15）

`DeltaDividedPowerIdeal.lean`で、I=φ⁻¹((p))を定義し、x∈I ↔ p∣x^pを証明した。
前工程の強帰納法を強め、p進階乗分母を正次数ならIの中に選べることを示した。
非p倍自然数の単元性を使って、n!を払う元も正次数ならI内に取れることまで証明した。
いずれの閉性にもp正則性は不要。δをIによる商へ降ろすことや、Iのδ安定性は仮定していない。
4公開宣言の対象2068ジョブとB4全体pure監査が成功。標準3公理のみ。
これでMathlib DividedPowers.ofInjectiveの閉性入力に使う実際のイデアルと分母が揃った。
この段階では分冪構造の公理・分冪包の普遍性・原典導来比較・CFF・一般B4は未完成。

### 次工程の登録：既存DividedPowersによる実際の分冪構造

BS専用`DeltaDividedPowers.lean`で、p正則なp局所δ環AのI={x | p∣x^p}に
Mathlibの既存DividedPowers構造を構成する。
A[1/p]への標準射の単射性と、非零整数の像の単元性によるℚ作用を使い、
RatAlgebra.dividedPowersをDividedPowers.ofInjectiveで引き戻す。
Iはpを含むため局所化像は全イデアルとなり、前工程の階乗分母の閉性をそのまま渡せる。
新しい分冪構造の概念・一般的な導来テンソル基盤は定義しない。
この構造は分冪包の普遍性やraw包の最小性・原典の導来比較・CFFとは別の工程。

## B4-6：実際の分冪構造と一意性（2026-10-15）

`DeltaDividedPowers.lean`で、p正則・p局所δ環AのI={x | p∣x^p}に
Mathlibの既存DividedPowersを構成した。p局所性は非p倍の自然数の単元性として明示する。
標準A[1/p]上の非零自然数の単元性と、既存IsLocalization.liftによるℚ作用を供給し、
RatAlgebra.dividedPowersをDividedPowers.ofInjectiveで引き戻した。
Iがpを含むため局所化像は全イデアルであり、前工程の正次数の階乗分母のI内閉性を使用した。
分冪公理を備えた実際の構造、階乗を掛けると通常冪になる式、I上の分冪構造の一意性を公開した。
private helperだけでなく公開するℚ作用と単元性の補題もBS監査対象へ追加した。
5公開宣言の対象2388ジョブ・最終B4全体pure監査が成功。標準3公理のみ。
新sorry・公理・外部引用は追加していない。G7・André引用は用いない。

この分冪構造はI上のものであり、(y)そのものが分冪閉イデアルだとは主張しない。
raw φ(y)/p包を分冪包と同定する普遍性・最小性、原典の導来pushout比較・CFF・一般B4は別工程。
全体ビルド/tmp/bs-factorialdivision-full.logは同じ実行を継続中。対象・pure監査成功と区別する。

### 次工程の登録：raw包の実分冪構造と既存分母の一致

BS専用`DeltaPDivisionDividedPowers.lean`で、既存raw包のp正則性を明示して
そのI={b | p∣b^p}上に前工程の既存DividedPowers構造を適用する。
基底元j(y)のI所属を初期p除算関係から供給し、分冪作用の値が
既存deltaPDivisionRawFactorialQuotientに一致することを示す。
比較はA[1/p]への既存の具体的単射と階乗の単元性で証明し、選択の一致を仮定しない。
p正則性に用いるAのp正則性・yのA/p正則性・自由δ環ghost単射・単元δp、
非p倍自然数の単元性を中間入力として明示する。
最終B4への仮定追加や、raw包の分冪包普遍性の証明済み扱いは行わない。

### 次工程の登録：raw包の像のδ安定部分環としての最小性

BS専用`DeltaPDivisionRawMinimal.lean`で、任意δ射f:raw→Tに対して、
fの基底射の像と初期除算変数の像を含むδ安定部分環Sにはf.rangeが含まれることを示す。
相対自由δ環の全座標の像の反復δ表示と、多項式・商の帰納法を使う。
具体的なf: A{φ(y_s)/p}→A[1/p]には、初期変数をy_s^p/p+δ(y_s)と書き、
Aとy_s^p/pを含むδ安定部分環への最小性として特殊化する。
p正則性・p局所性・G7・分冪構造の仮定は不要。単射性や分冪包のδ安定性は別途確認する。

## B4-6：具体的raw包への分冪構造の接続（2026-10-15）

`DeltaPDivisionDividedPowers.lean`で、rawφ除算包の基底元j(y)のp除算可能イデアルへの所属、
正則一元入力の仮定の下での実分冪構造を公開した。
その分冪作用の値が既存deltaPDivisionRawFactorialQuotientと一致することを、
実際のA[1/p]への既存単射と階乗の単元性により証明した。
選択で取った元の一致を仮定せず、階乗を払う両側の式から比較した。
3公開宣言の対象3787ジョブとB4全体pure監査が成功。標準3公理のみ。
一般B4・CFF・原典導来比較・分冪包普遍性は未完成。

継続していた全体ビルド/tmp/bs-factorialdivision-full.logは終端失敗を確認した。
共有Paper/Section5/SelectedParameterPositivity.lean:1で
共有KTheory/Adams/TensorSquareShuffle.oleanが欠落していた。
対象ビルド・pure監査の成功と全体ビルド成功を区別し、共有ファイルは変更していない。

### 次工程の登録：局所化内の具体的な階乗生成部分環との比較

BS専用`DeltaPDivisionFactorialSubring.lean`で、A[1/p]内のAと全y_s^n/n!の生成部分環を
既存Subring.closureで定義する。分冪包の別概念・普遍性は定義しない。
p局所性を明示し、raw包の具体的な階乗分母の像がこの正規化された局所化元になること、
この生成部分環がrawδ評価の像に含まれることを証明する。
y_s^p/pが生成部分環に入る計算を行い、前工程の最小性から、
生成部分環のδ安定性を明示した場合の逆包含・一致を示す。
δ安定性の入力を未解消のまま無条件の分冪包同定やCFFとは数えない。

## B4-6：raw像のδ安定部分環としての最小性（2026-10-15）

`DeltaPDivisionRawMinimal.lean`で、任意のrawδ包からのδ射について、
基底と初期除算変数の像を含むδ安定部分環は射の全像を含むことを証明した。
実際の相対自由δ環の全座標の像のδ反復表示と、通常多項式・商の帰納法で示した。
具体的なrawφ除算評価の像には、Aとy_s^p/pを含むδ安定部分環としての最小性を供給した。
p正則性・有限性・p局所性・G7は仮定しない。
2公開宣言の対象3767ジョブ・B4全体pure監査が成功。標準3公理のみ。
この最小性へ分冪生成部分環を渡すには、そのδ安定性を別途証明する必要がある。
CFF・原典導来比較・分冪包普遍性・一般B4は未完成。

### 次工程の登録：Lemma 2.36の具体的な有理係数のp可積分性

BS専用`DeltaDividedPowerCoefficients.lean`で、n>0、i≤nのとき
c_(n,i)=((pi)!/i!)*(p^(n-i)/(n-i)!)/p のp進付値が非負であることを証明する。
既存padicValRatと階乗付値公式を用い、val_p c_(n,i)=n−val_p((n−i)!)−1と計算する。
またd_n=(pn)!/((n!)^p*p)の付値非負を示す。
これらはφ(y^n/n!)/pと(y^n/n!)^p/pの展開係数に対応する。
非負付値から既約分母がpで割れないことも既存の有理数の既約性から供給する。
この係数計算だけで生成部分環のδ安定性や原典分冪包同定・CFFを結論しない。

## B4-6：具体的な階乗生成部分環とraw像の比較（2026-10-15）

`DeltaPDivisionFactorialSubring.lean`で、A[1/p]内のAと全y_s^n/n!の生成部分環を具体化した。
raw包の既存の階乗分母の像がこの正規化された局所化元と一致することを証明し、
生成部分環⊆rawδ評価の像を示した。y_s^p/pが(p−1)!γ_p(y_s)として部分環に入る計算も公開した。
生成部分環のδ安定性を明示すれば、前工程の最小性による逆包含と一致が従う。
この最後の定理はδ安定性入力に相対的であり、その入力を解消したとは数えない。
全σを許し、p局所性を要求する。p正則性・G7・André引用は用いない。

8公開宣言と前工程の最小性2定理の対象2402ジョブ・個別pure監査・B4全体pure監査が成功。
標準3公理のみ。新sorry・公理・引用なし。
当初の対象ビルドは共有CochainTensorLinearity.leanが欠落して停止した。
最小性モジュールが使わないRawRegular経路をRawEmbedding経由でimportしていたため、
自分の新規RawMinimalモジュールだけを、必要なDeltaPDivisionLocalizationへの直接importに変更した。
初期変数の像は既存の標準式とφ(y)=y^p+pδ(y)から直接計算し、共有ファイルは変更していない。
一般B4・CFF・原典導来比較・分冪包普遍性は未完成。

### 次工程の登録：p可積分な有理係数を実基底の像へ移す

BS専用`DeltaDividedPowerCoefficientImage.lean`で、p局所性を明示し、
q:ℚ、0≤val_p(q)なら、A[1/p]におけるqの像がAの標準像に入ることを証明する。
既約分母の非p倍性からA内の単元逆数と整数分子を使って具体的な原像を与える。
ℚ作用は既存primeDividedPowersAwayRatAlgebraを再利用し、別の有理数作用は定義しない。
前工程の2種類の展開係数へ適用し、局所化内の係数が基底像に入る公開定理を供給する。
G7・p正則性・完備性は要求しない。

## B4-6：Lemma 2.36の展開係数のp可積分性（2026-10-15）

`DeltaDividedPowerCoefficients.lean`で、Frobenius展開と冪の展開に対応する具体的有理係数を定義した。
前者の付値はn−val_p((n−i)!)−1、後者はn−(p−1)val_p(n!)−1と正確に計算した。
n>0、前者ではi≤nの下で双方が非負であることをMathlibの既存階乗付値公式から証明した。
有理数の既約性を使い、非負付値なら既約分母がpで割れないことも供給した。
これらはφ(γ_n(y))/pとγ_n(y)^p/pの係数への入力であり、展開恒等式そのものは別途必要。
7公開宣言の対象1171ジョブとB4全体pure監査成功。標準3公理のみ。
δ安定性・原典分冪包普遍性・導来比較・CFF・一般B4は未完成。

### 次工程の登録：分冪展開係数の恒等式と実Q代数での展開

BS専用`DeltaDividedPowerExpansion.lean`で、前工程の有理係数と二項係数の恒等式を証明する。
具体的にはc_(n,i)/(pi)! = choose(n,i)*p^(n-i)/(p*n!)、
d_n/(pn)! = 1/(p*(n!)^p)を、既存choose_mul_factorial_mul_factorialで示す。
その後、任意ℚ代数で(x^p+pz)^n/(p*n!)と(x^n/n!)^p/pを、
γ_(pi)(x)、γ_(pn)(x)を用いて実際に展開する。
環は整域とは仮定せず、ℚ→環の既存環射で係数恒等式を移す。
これを局所化の既存δ構造のφへ適用するのは次の工程。

## B4-6：p可積分展開係数の実基底像（2026-10-15）

`DeltaDividedPowerCoefficientImage.lean`で、p局所環Aと非負p進付値の有理数qに対して、
既存ℚ作用によるqのA[1/p]内の像が、実際にAの標準射の像に入ることを証明した。
既約分母のA内の単元逆数と整数分子から原像を与え、分母を掛けた等式で確認した。
Frobenius分冪展開・冪の分冪展開の2係数へ適用した公開定理も供給した。
p正則性・完備性・G7は不要で、零環も許す。
3公開宣言の対象2390ジョブ・B4全体pure監査成功。標準3公理のみ。
δ安定性・分冪包普遍性・原典導来比較・CFF・一般B4は未完成。

### 次工程の登録：実局所化δ構造での階乗生成元のδ展開

BS専用`DeltaPDivisionFactorialDelta.lean`で、正規化された局所化内のγ_n(y_s)を
既存ℚ作用による(1/n!)y_s^nとして書き、そのFrobenius像とδ像の実展開を証明する。
δ像は前工程のFrobenius係数による有限和から冪係数によるγ_(pn)を引いた形とする。
p局所性を明示し、既存の局所化δ構造とδ射の自然性を使う。
係数が基底像に入る証明と合わせ、各階乗生成元のδが具体的階乗生成部分環に入ることを示す。
部分環全体のδ安定性への拡張は、δ加法のWitt繰上り項と部分環生成帰納法で別途検証する。

## B4-6：実際の分冪展開恒等式（2026-10-15）

`DeltaDividedPowerExpansion.lean`で、付値計算した係数が二項係数と階乗の標準式に一致することを証明した。
その等式を任意の環射f:ℚ→Rに沿って移し、(x^p+f(p)z)^n/(p*n!)とγ_n(x)^p/pの
実際の分冪展開を公開した。Rは可換環であり、整域・非零環・p正則性は要求しない。
既存add_powと自然数のchoose_mul_factorial_mul_factorialを再利用した。
4公開定理の対象1193ジョブ・B4全体pure監査成功。標準3公理のみ。
これらの恒等式と前工程の係数の基底像を、実局所化δ構造へ接続している。
δ安定性・分冪包普遍性・原典導来比較・CFF・一般B4は未完成。

### 次工程の登録：階乗生成部分環のδ安定性とraw像の無条件同定

BS専用`DeltaPDivisionFactorialStable.lean`で、まず任意部分環のWitt繰上り項の閉性を示し、
δの加法・乗法公式と部分環生成帰納法により、生成元でのδ所属から全体のδ安定性へ拡張する。
実階乗生成部分環には、基底上のδ自然性と前工程の各階乗生成元のδ所属を供給する。
これにより前工程のδ安定性入力を解消し、p局所性だけの下で具体的な階乗生成部分環と
rawδ評価の実像との一致を証明する。
像の一致をraw環自体の単射性・導来pushoutの離散性・分冪包普遍性・CFFとは同一視しない。

## B4-6：実局所化δ作用での階乗生成元の展開（2026-10-15）

`DeltaPDivisionFactorialDelta.lean`で、Ring.inverseによるγ_n(y_s)を既存ℚ作用による
(1/n!)y_s^nに一致させ、既存の局所化Frobeniusとδを直接計算した。
δ(γ_n(y_s))を、p可積分係数によるγ_(pi)(y_s)の有限和とγ_(pn)(y_s)の差として書き下した。
前工程の係数の実基底像を供給し、すべての階乗生成元の実δ像が具体的階乗生成部分環内に入ることを示した。
n=0はδ(1)=0で別に処理し、正次数の係数の可積分性を0へ誤用していない。
4公開定理の対象2406ジョブ・B4全体pure監査成功。標準3公理のみ。
p局所性を明示し、p正則性・完備性・G7・André引用は用いない。
全体のδ安定性はWitt繰上り項を含む生成帰納法を現在検証中。
分冪包普遍性・原典導来比較・CFF・一般B4は未完成。

## B4-6：階乗生成部分環のδ安定性とraw像の無条件同定（2026-10-15）

`DeltaPDivisionFactorialStable.lean`で、Wittベクトルの部分環包含に沿う自然性を用い、
Witt加法の繰上り項が部分環内にあることを証明した。
δの加法・乗法・加法逆元の式とSubring.closure_inductionにより、生成元での所属を全体へ拡張した。
実際の階乗生成部分環には基底上のδ自然性と前工程のδ生成元の展開を供給した。
これにより、前工程で明示していたδ安定性入力を解消した。
p局所性だけの下で、Aと全y_s^n/n!の生成部分環がrawφ除算包の実局所化像に一致する。
さらにφ捻りを含むこの像が基底のδ構造の選び方に依存しないことも証明した。
任意σ・pねじれ・零環を許し、p正則性・G7・André引用は用いない。

5公開定理の対象2407ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・外部引用なし。
像の一致であり、raw環自体の単射性や原典の導来pushoutの離散性を無条件に結論しない。
分冪包普遍性・原典導来比較・CFF・一般B4は未完成。
全体ビルド/tmp/bs-factorialstable-full.logは別途継続中。

### 次工程の登録：正則一元raw包と具体的階乗生成部分環の環同型

BS専用`DeltaPDivisionFactorialEquiv.lean`で、既存raw評価の単射性と前工程の像の一致を合成し、
実raw環A{φ(y)/p}とA[1/p]内の具体的階乗生成部分環の標準環同型を構成する。
標準評価・基底A・各階乗分母の像の式を公開する。
Aのp正則性・yのA/p正則性・自由δ環ghost単射・単元δp・p局所性を中間入力として保持する。
これは通常環の明示的同型であり、原典の導来pushout比較・分冪包普遍性・CFFとは区別する。

## B4-6：正則一元raw環の標準同型の検証境界（2026-10-15）

`DeltaPDivisionFactorialEquiv.lean`に、既存raw評価の単射性と階乗生成部分環との像の一致を
合成する標準環同型、局所化値・基底・階乗分母の3つの式を実装した。
直接Lean型検査は成功し、同じソースへ4宣言のassert_no_sorryと#print axiomsを付けた
/tmp/bs-factorialequiv-source-audit.leanも成功した。依存は標準3公理のみ。
これは現在の共有依存オブジェクトを用いた直接検証として記録する。

通常の対象ビルド/tmp/bs-factorialequiv-build.logは、共有CochainTensorScalarCone.lean:36,59の
mappingCone.fst/snd未解決で停止した。共有ソースの通常再ビルド成功とは区別する。
このraw環の同型モジュールは、この時点ではコミットせず、通常対象の再検証待ちとして保持する。
B4全体監査への4宣言のimport/assert追加も通常対象の成功後に行う。
待つのはこの正則性経路に依存する検証だけであり、階乗部分環のδ安定性・raw像との一致の
36公開宣言（このターンの8工程分）の対象ビルド・pure監査は成功済みとして区別する。

全体ビルド/tmp/bs-factorialstable-full.logも終端失敗を確認した。
共有KTheory/Adams/KoszulSquareCoordinates.lean:72,96のmappingConeを含む式のrewriteが失敗した。
共有ファイルは変更していない。全体ビルドを成功とは報告しない。
この時点の対象・監査・全体ビルドの全実行は終端を確認した。

次は通常raw環の同型の検証を共有依存の修正後に再開する。
並行して独立に進められる実分冪構造・具体的階乗部分環の普遍性や表示を調べる。
現時点では、像の一致と分冪包の普遍性、通常環の同型と原典の導来δpushout比較、
G7待ちの全源Tor移送とCFF根付き拡大の存在をそれぞれ区別し、一般B4は未完成として保持する。

### 次工程の登録：δ安定部分環への既存δ構造の制限

BS専用`DeltaSubring.lean`で、既存DeltaStructure.ofFunctionを使い、
δ安定部分環S⊆Aに元のδ構造を制限する。
Witt繰上り項の自然性を含めてδ加法・乗法の恒等式を確認し、包含がδ射であること、
包含をδ射にするδ構造の一意性を示す。新たなδ環の概念は導入しない。
利用先は具体的階乗生成部分環の実分冪構造であり、p正則性や共有Tor基盤には依存しない。

## B4-6：保留した正則raw環の標準同型の再検証（2026-10-15）

現在の共有依存でDeltaPDivisionFactorialEquivの通常対象3795ジョブとB4全体pure監査が成功した。
前回のCochainTensorScalarConeの停止は今回再現せず、4宣言の監査も標準3公理のみだった。
これにより、正則一元raw環と局所化内の具体的階乗生成部分環の標準環同型、
標準評価・元の基底・階乗分母の像の式を通常ビルドで検証済みの成果として確定する。
Aのp正則性・yのA/p正則性・自由δ環ghost単射・単元δp・p局所性という中間入力は保持する。
前回の直接検証成功と今回の通常対象成功を区別し、保留していたモジュールをここでコミットする。
分冪包普遍性・原典導来比較・CFF・一般B4は未完成。

### 次工程の登録：具体的階乗生成部分環のδ構造・p正則性・分冪作用

BS専用`DeltaPDivisionFactorialStructure.lean`で、A→階乗生成部分環の実基底射を定義し、
前工程のδ安定性から既存の局所化δ構造を制限する。
pがA[1/p]で単元であることから部分環でのp正則性を証明する。
p局所性を実基底射で移して、既存primeDividedPowersを部分環内のp除算可能イデアルへ適用する。
基底元y_sの所属と、その分冪作用の値が具体的なy_s^n/n!となる式を公開する。
任意σ・Aのpねじれを許し、元のAのp正則性・ghost単射・G7は要求しない。
最大p除算可能イデアル上の分冪構造と、正次数の階乗生成元からなる分冪包イデアルは区別する。

## B4-6：δ安定部分環へのδ構造の制限（2026-10-15）

`DeltaSubring.lean`で、既存DeltaStructure.ofFunctionによりδ安定部分環へδ構造を制限した。
Witt加法繰上り項の自然性と元のδ恒等式を確認し、制限したδの具体式、包含のδ射性、
包含をδ射にする構造の一意性を公開した。p正則性は不要。
4公開宣言の対象2053ジョブ・B4全体pure監査成功。標準3公理のみ。
新しいδ環概念・公理・sorry・外部引用は追加していない。
具体的階乗生成部分環の実分冪構造へ適用する。

### 次工程の登録：正次数の階乗分母が生成する実際の分冪イデアル

BS専用`DeltaPDivisionFactorialIdeal.lean`で、具体的部分環内の全γ_(n+1)(y_s)の生成イデアルJを
δ構造と独立に定義する。前工程の最大p除算可能イデアル上の分冪構造を用い、
Mathlibの既存SubDPIdeal.spanとspan_carrier_eq_dpow_spanによりJが実分冪イデアルであることを示す。
これに既存IsSubDPIdeal.dividedPowersを制限し、J上の実分冪構造と基底元上の正規化を公開する。
(y)自体が分冪閉であるとは仮定しない。Jの分冪構造と分冪包の普遍性は区別する。
元のAのp正則性・有限性・ghost単射・G7は要求しない。

## B4-6：具体的階乗生成部分環の実δ構造と分冪作用（2026-10-15）

`DeltaPDivisionFactorialStructure.lean`で、実基底射A→S、局所化の既存δ作用のSへの制限、
基底射と包含のδ射性を公開した。pが局所化内で単元であることからS内のp正則性を示した。
元のAのp正則性は使わず、p局所性を実基底射で移して既存primeDividedPowersをS内の
最大p除算可能イデアルへ適用した。基底元y_sの所属と、分冪作用の値が実際のy_s^n/n!に
一致することを、局所化内の階乗の単元性で確認した。
任意σ・元のAのpねじれ・零環を許し、ghost単射・G7・André引用は用いない。
8公開宣言の通常対象・後続との結合ビルド・B4全体pure監査が成功。標準3公理のみ。
新sorry・公理・引用なし。分冪包の正次数イデアル・普遍性・導来比較・CFF・一般B4は別工程。

## B4-6：正次数階乗イデアル上の実分冪構造（2026-10-15）

`DeltaPDivisionFactorialIdeal.lean`で、全γ_(n+1)(y_s)が生成する具体的イデアルJを
δ構造と独立に定義し、y_s=γ_1(y_s)の所属を確認した。
Mathlib SubDPIdeal.span_carrier_eq_dpow_spanと前工程の分冪値の正規化により、
Jが基底元の実分冪生成イデアルそのものであることを示した。
既存IsSubDPIdeal.dividedPowersをJへ制限し、J上の実際の分冪構造と基底元上の式を公開した。
(y)自体を分冪閉と仮定せず、最大p除算可能イデアルとJを区別している。
任意σ・元のAのpねじれを許し、p局所性だけを要求する。
6公開宣言の対象2413ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。分冪包の普遍性・原典導来比較・CFF・一般B4は未完成。

### 次工程の登録：具体的階乗部分環と正次数イデアルの関手的な実写像

BS専用`DeltaPDivisionFactorialMap.lean`で、環射f:A→Bに対してMathlibの既存IsLocalization.mapを
p局所化へ特殊化し、具体的階乗生成部分環S(A,y)→S(B,f∘y)への制限を構成する。
源のp局所性を明示して階乗逆数の像を確認し、実基底射と各階乗生成元の像の式を示す。
正次数階乗イデアルが対応する標的イデアルへ写ることも証明する。
新たな局所化・分冪包・共通Torの定義は導入しない。
この実写像を使った一般の導来基底変更・平坦性は別工程。

### 次工程の登録：階乗生成部分環の射の一意性と関手性

BS専用`DeltaPDivisionFactorialFunctorial.lean`で、基底Aと全階乗生成元上で一致する
具体的部分環からの環射が一意に一致することを部分環生成帰納法で示す。
これにより、前工程の実誘導射が恒等射と合成を保つことを証明する。
既存perfectoid化の一意性とは別の具体的部分環の生成元による射の判定であり、
同等のperfectoid化の概念・一意性定理は重複しない。

### 次工程の登録：具体的な誘導環射の分冪射性

BS専用`DeltaPDivisionFactorialDPMorphism.lean`で、前工程の実誘導環射が
正次数階乗イデアル上の実分冪構造を保つことを証明する。
イデアルの像の包含を供給し、任意のイデアル元のn番目分冪について、
階乗を掛けた両側の通常冪の式と標的局所化内の階乗の単元性で一致を示す。
基底射fのδ射性を仮定せず、A,Bのp局所性と各δ構造を明示する。
Mathlib IsDPMorphismを使用し、別の分冪射の概念は作らない。

## B4-6：階乗部分環と正次数イデアルの実誘導射（2026-10-15）

`DeltaPDivisionFactorialMap.lean`で、f:A→Bに対し既存IsLocalization.mapをp局所化へ特殊化し、
源のp局所性を明示してS(A,y)→S(B,f∘y)の実環射を構成した。
実基底射との可換性、すべての階乗生成元の標準像、正次数階乗イデアルの像の包含を証明した。
局所化や階乗逆数が無条件に写るとはせず、階乗の源での単元性を明示して既存map_ringInverseを用いた。
任意元族・異なる環のuniverse・pねじれを許し、元のAのp正則性・fのδ射性・G7は要求しない。
8公開宣言の対象2414ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。一般導来基底変更・平坦性・CFF・一般B4は未完成。

### 次工程の登録：誘導された実階乗部分環射のδ射性

BS専用`DeltaPDivisionFactorialDeltaMap.lean`で、基底環射f:A→Bが既存δ構造を保つ場合、
既存existsUnique_localization_liftと標準射上の式による一意性を使い、
前工程の実局所化写像がδ射であることを示す。
具体的階乗部分環への制限についても、包含とδ作用の制限の式からδ射性を証明する。
p正則性・完備性・G7は要求せず、既存IsDeltaHomを使う。

## B4-6：具体的階乗部分環の射の一意性・関手性（2026-10-15）

`DeltaPDivisionFactorialFunctorial.lean`で、元の基底と全階乗生成元上で一致する環射の一致を、
Subring.closure_inductionにより証明した。
これを用い、実誘導射が恒等射と合成を保つことを公開した。
任意の可換試験環・異なるuniverseを許し、perfectoid化の一意性とは別の具体的生成元の判定である。
3公開定理の対象2415ジョブ・新規12宣言の個別pure監査・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。
一般導来基底変更・CFF・一般B4は未完成。

## B4-6：実誘導環射の分冪射性（2026-10-15）

`DeltaPDivisionFactorialDPMorphism.lean`で、実誘導環射が正次数階乗イデアル上の
全元の全分冪を保つことを、Mathlib IsDPMorphismとして証明した。
イデアル像の包含を供給し、階乗を掛けた両側の通常冪の等式を標的局所化内で消去した。
基底環射のδ射性や元のA,Bのp正則性は要求せず、両側のp局所性とδ構造を明示する。
1公開定理の対象2415ジョブ・新規12宣言の個別pure監査・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。
分冪包の普遍性・一般導来比較・CFF・一般B4は未完成。

## B4-6：実誘導階乗部分環射のδ射性（2026-10-15）

`DeltaPDivisionFactorialDeltaMap.lean`で、基底δ射に沿う実p局所化写像がδ射であることを、
既存existsUnique_localization_liftと標準基底射上の一意性から証明した。
具体的階乗部分環への制限も、既存δ作用の制限を保つδ射であることを公開した。
p正則性・完備性・G7は要求しない。別のδ射の概念や局所化は定義していない。
2公開定理の対象2415ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。一般導来比較・平坦性・CFF・一般B4は未完成。

## 共通基盤要求G3・G6・G7の送信記録（2026-10-15）

ユーザーの明示許可「3件を送ってよい」に基づき、現在の「CLMST」チャット
（01a13993-b4ee-7a10-8441-7d21224139d7）へ3件を送信し、ツールの成功を確認した。
正確な仮定・結論、追加しない仮定、利用工程、既存APIの不足を送付した。
G3は正則主元と剰余平坦性から既存IsCompletelyFlatへの判定、G6は導来完備環の
完備化元のJacobson根基への所属、G7はextendScalarsのleftDerivedとℕ-colimitの交換である。
これは送信済みの記録であり、実装受領・依存解消を意味しない。
共有ファイルの編集や追加のチャット間送信の許可へは拡張しない。
BS側ではこの3件を待つ適用箇所を保留し、独立した構成・証明を続ける。

### 今回の全体ビルドの検証境界

実行中だった全体lake buildは終了コード1で終了した。
ログは /tmp/bs-factorialideal-full.log。共有PerfectComplex等の複数対象が失敗し、
ModuleSupport.olean、ClosedSupportGeometry.oleanの欠落も報告された。
この全体検証を成功とは数えず、直前のBS対象ビルド・B4全体pure監査の成功と区別する。
共有ファイルの修正は行っていない。一般B4・導来比較・必要なCFF拡大の存在は未完成。

### 次工程の登録：既存分冪イデアルに対する階乗部分環の退化

BS専用DeltaPDivisionFactorialPDTarget.leanで、p局所環Aの既存分冪イデアルIに
元族yが入る場合、具体的階乗部分環S(A,y)がA→A[1/p]の像そのものであることを証明する。
分冪の階乗恒等式から各階乗生成元を実分冪値の像に同定し、基底射A→Sの全射性を得る。
この像の同定にはAのp正則性を要求しない。p正則性を明示した場合のみ基底射の単射性と
実環同型A≃Sを構成する。これは分冪標的への普遍射構成の入力であり、
一般の分冪包の普遍性・導来比較・CFFを完了したとは数えない。

## B4-6：既存分冪標的での具体的階乗部分環の同定（2026-10-15）

DeltaPDivisionFactorialPDTarget.leanで、p局所環の分冪イデアルIに元族yが入る場合、
各階乗分母が実分冪値の局所化像に一致すること、およびS(A,y)が基底の像そのもので
あることを証明した。基底射A→Sの全射性にはpねじれを許す。
p正則性を明示した場合に基底射の単射性と実環同型A≃Sも構成した。
δ構造は仮定せず、既存DividedPowersの階乗恒等式と局所化APIを再利用した。
5公開宣言の対象2411ジョブとB4全体pure監査に成功。標準3公理のみ。
新sorry・公理・引用なし。一般分冪包の普遍性・導来比較・CFF・一般B4は未完成。

### 次工程の登録：p正則分冪標的への実延長射と一意性

BS専用DeltaPDivisionFactorialPDLift.leanで、p局所環A,B、環射f:A→B、
Bの分冪イデアルIとf(y_s)∈I、Bのp正則性を明示し、S(A,y)→Bの実環射を構成する。
既存の基底変更射と前工程の標的同型の逆を合成する。
階乗生成元上の分冪値の式を証明し、階乗恒等式とB[1/p]内の消去により、
基底上の延長条件のみから環射の一意性を示す。
このp正則な標的に限った結果を一般のpねじれ分冪標的の普遍性と混同しない。
G3・G6・G7、δ構造、André引用は用いない。

## B4-6：p正則な分冪標的への実延長射と一意性（2026-10-15）

DeltaPDivisionFactorialPDLift.leanで、A,Bのp局所性、Bのp正則性、Bの分冪イデアルI、
f:A→Bとf(y_s)∈IからS(A,y)→Bの実環射を構成し、基底射との可換性と
全階乗生成元の像がH.dpow n (f(y_s))であることを証明した。
また基底上で一致する任意の環射S(A,y)→Bが一致することを、具体的階乗恒等式と
B[1/p]への単射・階乗の単元性による消去から証明した。
従って基底射を延長する環射の存在と一意性が、p正則な分冪標的について成立する。
6公開宣言の対象2417ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。一般のpねじれ分冪標的への普遍性、導来比較、CFF、一般B4は未完成。

### 次工程の登録：p正則分冪標的への延長射の分冪射性

BS専用DeltaPDivisionFactorialPDUniversal.leanで、前工程の実延長射が
正次数階乗イデアルを標的分冪イデアルへ写し、すべての分冪を保つことを証明する。
源に既存のδ由来の実分冪構造を使い、標的には任意の既存DividedPowersを許す。
既存IsDPMorphismを用い、基底射を延長する分冪射の存在と一意性をp正則標的に限定して公開する。
一般pねじれ標的への普遍性・導来比較・CFFとは分ける。

## B4-6：p正則分冪標的に対する分冪射の普遍性（2026-10-15）

DeltaPDivisionFactorialPDUniversal.leanで、実延長射が正次数階乗イデアルを
標的の指定された分冪イデアルへ写すことと、全元の全分冪を保つことを証明した。
源は既存δ由来の実分冪構造、標的は任意の既存DividedPowersであり、標的のδ構造を要求しない。
p正則な標的に限定した、基底射を延長するMathlib IsDPMorphismの存在と一意性を公開した。
3公開定理の対象2418ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。p正則性を最終B4の仮定へ追加してはならず、
一般pねじれ分冪標的の普遍性・導来比較・CFF根付き拡大・一般B4は未完成。

共通計画clmst.mdの「共通基盤の追加要求受領（2026-10-15）」でG3・G6・G7の
受領記録を確認した。送信の到達は確認済みだが、公開APIの実装受渡しはまだ完了していない。
共通ファイルの編集・追加メッセージ送信は行っていない。

### 次工程の登録：一元分冪表示環と一般分冪標的への評価

BS専用PrincipalDPPresentation.leanに、Mathlib DividedPowerAlgebra A Aの
γ₁(1)−yによる商環を作る。既存liftを利用して、任意のA代数Bの既存分冪イデアルに
yの像が入る場合の実評価射を構成し、全γ_n(1)上の式・生成元上の一意性を証明する。
標的のp正則性・p局所性を要求しない。この表示環に分冪構造があることや
既存階乗部分環との同型はまだ主張しない。後者の単射性には原典の正則性の入力が必要。
一般の分冪包・Tor基盤の重複定義はせず、Mathlibの既存代数と実商のみを用いる。

## B4-6：一元分冪表示環とねじれを許す標的への実評価（2026-10-15）

PrincipalDPPresentation.leanで既存DividedPowerAlgebra A Aにγ₁(1)=yを課した
実商環を定義し、全γ_n(1)の階乗恒等式を証明した。
任意の可換A代数B、既存分冪構造H:I、yの像のIへの所属から、
γ_n(1)をH.dpow n (yの像)へ送る実代数射を構成し、その生成元値を指定した
存在・一意性を証明した。p正則性・p局所性・δ構造は要求せず、ねじれ標的も許す。
既存DividedPowerAlgebra.liftと商APIを再利用し、一般分冪代数を重複構築していない。
9公開宣言の対象1524ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。表示環自身の分冪構造、階乗部分環との同型、
一般分冪包の普遍性、導来比較、CFF、一般B4は未完成。

### 次工程の登録：一元分冪表示環から実階乗部分環への全射

BS専用PrincipalDPToFactorial.leanで、p局所δ環Aの一元yについて、
前工程の表示環から具体的階乗部分環S(A,y)への実環射を構成する。
Sの正次数イデアルの既存分冪構造へprincipalDPEvalを適用し、
基底射との可換性、全γ_n(1)の具体的階乗分母への像、全射性を証明する。
Aのp正則性を仮定せず、単射性や原典の分冪包比較・導来比較とは区別する。

## B4-6：一元分冪表示環から階乗部分環への実全射（2026-10-15）

PrincipalDPToFactorial.leanで、p局所δ環Aの一元yについて、既存正次数イデアルの
実分冪構造への評価からPrincipalDPPresentation A y→S(A,y)を構成した。
基底射との可換性、全標準生成元の像が具体的階乗分母になること、全射性を証明した。
Aのp正則性は要求しない。4公開宣言の対象2418ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。
単射性・表示環自身の分冪構造・原典の分冪包比較・導来比較・CFF・一般B4は未完成。

### 次工程の登録：表示環から階乗部分環への全射の核

BS専用PrincipalDPFactorialKernel.leanで、実全射の核が表示環のp局所化写像の核に
一致することを証明する。A[1/p]→表示環[1/p]の標準局所化延長を用い、
全標準生成元の階乗恒等式で表示環上の合成を同定する。
逆包含には既存の階乗部分環のp正則性を用いる。
これにより残る単射性を表示環のp冪ねじれ消滅へ帰着するが、正則一元入力での
表示環のp正則性自体はまだ別工程とし、最終B4へ仮定を追加しない。

## B4-6：表示環から階乗部分環への全射の核の同定（2026-10-15）

PrincipalDPFactorialKernel.leanで、実全射の核が表示環の実p局所化の核に一致することを証明した。
局所化の標準延長と表示環の全生成元の階乗恒等式により、一方向の核包含を示した。
逆方向には既存の具体的階乗部分環のp正則性を用いた。
さらに、実全射で零になる元が、ちょうど表示環内であるp冪により消える元であることを公開した。
Aのp正則性を仮定しない。4公開定理の対象2419ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。
残る単射性には、原典の正則一元入力の下で表示環のp冪ねじれが消えることの証明が必要。
表示環自身の分冪構造、一般分冪包の普遍性、導来比較、CFF、一般B4は未完成。
今後は既存DividedPowerAlgebra A Aの一元基底と、γ₁(1)−yのmod p正則性を具体化し、
既存のisSMulRegular_quotient_span_of_regular_modへ接続する。

### 次工程の登録：既存一元分冪代数の基底

BS専用RankOneDPBasis.leanで、既存DividedPowerAlgebra A Aがγ_n(1)でA線形生成されることを
既存の帰納法・積公式から証明する。Aが可換ℚ代数Cへ単射に写る場合には、
C[X]の全イデアルの標準分冪構造への既存liftを使い、γ_n(1)をX^n/n!へ送る評価射を作る。
多項式係数で線形独立性を示し、実際のModule.Basisを構成する。
後続でp局所・p正則なAにはC=A[1/p]を用いる。一般の分冪代数を重複定義しない。

## B4-6：既存一元分冪代数の具体的基底（2026-10-15）

RankOneDPBasis.leanで、任意の可換環A上の既存DividedPowerAlgebra A Aが
γ_n(1)で線形生成されることを既存帰納法・積公式から証明した。
Aが可換ℚ代数Cへ単射に写る場合、C[X]の標準分冪構造への実評価射を作り、
γ_n(1)の像がC(1/n!)X^nであることと、係数比較による線形独立性を証明した。
実際のModule.Basis ℕ A (DividedPowerAlgebra A A)と各標準元上の式を公開した。
6公開宣言の対象1516ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。一般分冪代数の定義は重複していない。
商のp正則性・分冪包比較・導来比較・CFF・一般B4は未完成。

### 次工程の登録：p局所・p正則な係数環での一元分冪基底

BS専用RankOneDPPrimeBasis.leanで、p局所・p正則なAについてC=A[1/p]を用い、
前工程の実基底を特殊化する。既存の局所化内ℚ代数と基底射の単射性を再利用する。
実基底によるModule.Freeを供給し、既存Module.Flat.isSMulRegular_of_isRegularから
DividedPowerAlgebra A A自身のp正則性を導く。
正則な一元を課した商のp正則性は次工程であり、δ構造や完備性は要求しない。

## B4-6：p局所係数での実一元分冪基底とp正則性（2026-10-15）

RankOneDPPrimeBasis.leanで、p局所・p正則なAに対し、実局所化A[1/p]の
既存ℚ代数構造と既存基底射の単射性を用いて実基底を特殊化した。
この実基底からModule.Freeを供給し、既存Module.Flat.isSMulRegular_of_isRegularを使い、
DividedPowerAlgebra A A自身のp正則性を証明した。δ構造・完備性は不要。
4公開宣言の対象2708ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。商のp正則性、分冪包比較、導来比較、CFF、一般B4は未完成。

### 次工程の登録：正則一元入力での分冪表示環のp正則性

BS専用PrincipalDPRegular.leanで、p局所・p正則なAとy mod pの正則性から、
表示環PrincipalDPPresentation A yのp正則性を証明する。
一元分冪代数内のγ₁(1)^pがpで割れることを階乗恒等式から示す。
係数yのmod p正則性は既存isSMulRegular_mod_of_flatで移送する。
γ₁(1)−yにより消える元について、γ₁(1)倍とy倍の一致をp回反復し、
γ₁(1)^p=0とy^pの正則性から零を得る。
最後に既存isSMulRegular_quotient_span_of_regular_modを使う。
Noetherian性・完備性・δ構造を追加しない。

## B4-6：正則一元分冪表示環のp正則性（2026-10-15）

PrincipalDPRegular.leanで、p局所・p正則なAとy mod pの正則性から、
具体的表示環PrincipalDPPresentation A y自身のp正則性を証明した。
一次生成元のp乗のp可除性を階乗恒等式から示し、係数yのmod p正則性を既存の
isSMulRegular_mod_of_flatで移送した。γ₁(1)倍とy倍の一致を反復して表示関係の
mod p正則性を得た後、既存isSMulRegular_quotient_span_of_regular_modを適用した。
Noetherian性・完備性・δ構造は不要。3公開定理の対象2733ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。
原典の分冪包比較・導来比較・CFF・一般B4は未完成。

### 次工程の登録：正則一元表示環と階乗部分環の実同型

BS専用PrincipalDPFactorialEquiv.leanで、p局所・p正則なδ環Aとy mod pの正則性の下、
前工程の表示環のp正則性と既存の核の同定を組み合わせ、実比較射の単射性を証明する。
既存全射性と合わせて環同型を構成し、基底と全標準生成元上の式を公開する。
Witt ghost単射やδ(p)の単元性はこの通常表示環の比較には要求しない。
原典の導来δpushout比較・CFFは別工程。

## B4-6：正則一元分冪表示環と実階乗部分環の同型（2026-10-15）

PrincipalDPFactorialEquiv.leanで、既存の核のp冪ねじれとの同定と表示環のp正則性から
実比較射の単射性を証明し、既存全射性と合わせて実環同型を構成した。
元のAからの基底射との可換性、全γ_n(1)の指定された階乗分母への像を公開した。
仮定はp局所・p正則なδ環Aとy mod pの正則性。Witt ghost単射・δ(p)の単元性・完備性は不要。
4公開宣言の対象2739ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。一般分冪標的への分冪射の普遍性の接続、導来比較、CFF、一般B4は未完成。

### 次工程の登録：正則一元入力の階乗部分環の一般分冪標的への普遍性

BS専用RegularPrincipalDPUniversal.leanで、p局所・p正則なδ環A、y mod pの正則性の下、
階乗部分環S(A,y)から任意の可換A代数Bの既存分冪イデアルへの実射を構成する。
Bにはp正則性・p局所性・完備性・δ構造を要求しない。
実表示環同型の逆とprincipalDPEvalを合成し、全階乗生成元の像を示す。
Mathlib IsDPMorphism.on_spanと分冪の合成公式を使って全分冪との両立を証明し、
基底射を延長する分冪射の存在と一意性を公開する。
原典の通常一元分冪包比較を進める工程であり、導来比較・CFFとは区別する。

## B4-6：正則一元階乗部分環の一般分冪標的への普遍性（2026-10-15）

RegularPrincipalDPUniversal.leanで、p局所・p正則なδ環Aとy mod pの正則性の下、
任意の可換A代数B、既存分冪構造H:I、yの像のIへの所属から、S(A,y)→Bの
実環射を構成した。基底射との可換性と全階乗生成元の具体的分冪値への像を証明した。
Bにはp正則性・p局所性・完備性・δ構造を要求せず、pねじれを許す。
Mathlib IsDPMorphism.on_spanと分冪合成公式を用い、全元の全分冪との両立を証明した。
基底射を延長する分冪射の存在と一意性を公開したため、正則一元入力についての
通常の分冪包の普遍性を、具体的階乗部分環と既存正次数イデアルに対して得た。
以前のp正則標的に限定した普遍性とは異なり、この成果には標的正則性の制限はない。
5公開宣言の対象2742ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。源のδ構造・p局所性・p正則性・y mod p正則性は明示している。
任意有限正則列への拡張、原典の導来δpushout比較、CFF根付き拡大、一般B4は未完成。
共通G3・G6・G7は共通計画上も受領済み・実装受渡し未完了であり、この成果には使っていない。

### 次工程の登録：既存一元分冪代数の実テンソル基底変更

BS専用RankOneDPBaseChange.leanで、既存DividedPowerAlgebra.mapとAlgebra.TensorProduct.liftから
B ⊗[A] DividedPowerAlgebra A A →ₐ[B] DividedPowerAlgebra B Bの実比較射を作る。
p局所・p正則な可換環A,Bについて、前工程の両側の実基底と基底のテンソル基底変更を
照合し、この射が同型であることを証明する。δ構造・完備性・Noetherian性は要求しない。
この通常代数の比較を、分冪表示環の商の基底変更・導来比較・CFFそのものとは数えない。

## B4-6：既存一元分冪代数の実テンソル基底変更（2026-10-15）

RankOneDPBaseChange.leanで、既存DividedPowerAlgebra.mapとTensorProduct.liftから
実比較射B⊗[A]Γ_A(A)→ₐ[B]Γ_B(B)を構成し、全純テンソルと標準基底上の式を公開した。
p局所・p正則な可換環A,Bの下、両側の実基底と基底のテンソル基底変更を照合して
全単射性および実代数同型を証明した。δ構造・完備性・Noetherian性は不要。
6公開宣言の対象2709ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。この通常代数の比較は商の分冪包比較・導来比較・CFFとは別工程。

### 次工程の登録：一元分冪表示環の実テンソル基底変更

BS専用PrincipalDPBaseChange.leanで、p局所・p正則な可換環A,BとA代数構造について、
B⊗[A]PrincipalDPPresentation A y ≃ₐ[B] PrincipalDPPresentation B (algebraMap A B y)
を構成する。前工程の実同型がγ₁(1)−yを対応する表示関係へ送ることを示し、
Mathlibのテンソル商同型と商環同型を合成する。
yの正則性・δ構造・完備性を要求せず、商環の基底変更を正確に扱う。
一般の導来テンソル比較・分冪包の平坦性・CFFは別工程。

## B4-6：一元分冪表示環の実テンソル基底変更（2026-10-15）

PrincipalDPBaseChange.leanで、実一元分冪代数比較射が表示関係を対応する関係へ送ること、
および拡大した表示関係イデアルの像の一致を証明した。
Mathlibの実テンソル商同型と商代数同型を合成し、
B⊗[A]PrincipalDPPresentation A y≃ₐ[B]PrincipalDPPresentation B (algebraMap A B y)
を構成した。Bの係数と全標準生成元の純テンソル上の式も公開した。
仮定はA,Bのp局所性・p正則性。yの正則性・δ構造・完備性・Noetherian性は不要。
5公開宣言の対象2711ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。原典の導来比較・分冪包の平坦性・CFF・一般B4は未完成。

### 次工程の登録：正則一元階乗部分環の実テンソル基底変更

BS専用RegularPrincipalDPBaseChange.leanで、p局所・p正則なδ環A,B、A代数B、
yとその像のmod p正則性の下、B⊗[A]S(A,y)≃ₐ[B]S(B,fy)を構成する。
表示環と階乗部分環の実同型を基底射との可換性によって代数同型へ持ち上げ、
前工程の実テンソル基底変更と合成する。Bの係数と階乗生成元の純テンソル上の式を公開する。
基底の環射のδ射性や完備性は要求しない。通常分冪包の基底変更であり、導来比較やCFFではない。

同じ工程で、実同型を既存pDivisionFactorialMapと比較し、全純テンソルb⊗aの像が
baseB(b)・pDivisionFactorialMap(a)であることも証明する。
生成元上だけの対応に留めず、具体的基底変更射として識別できる公開式を供給する。

## B4-6：正則一元分冪包の実テンソル基底変更（2026-10-15）

RegularPrincipalDPBaseChange.leanで、表示環の実同型を基底射との可換性により代数同型へ持ち上げ、
通常テンソル基底変更と合成してB⊗[A]S(A,y)≃ₐ[B]S(B,fy)を構成した。
具体的な基底射による代数構造を型に明示し、Bの係数と全階乗生成元の純テンソル上の式を証明した。
さらに全純テンソルb⊗aの像がbaseB(b)・pDivisionFactorialMap(a)であることを証明し、
既存の具体的部分環射による実比較写像として同定した。
仮定はp局所・p正則なδ環A,Bとy,fyのmod p正則性。基底射のδ射性・完備性は不要。
4公開宣言の対象2744ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。原典の導来比較・完全平坦性・CFF・一般B4は未完成。

### 全体ビルドの検証境界

前回開始した全体lake buildは、同じ実行ハンドルを継続して観測し、終了コード1を確認した。
ログは /tmp/bs-regular-principaldp-full-build.log。
共有RegularLocalization.lean:60のisResolutionOf_koszul未解決、および共有側の
BoundedHomotopy.olean、HomotopyCategory.olean、ClosedSupportK0.oleanの欠落が報告された。
BS対象ビルド・専用pure監査の成功と、全体ビルドの失敗は分けて扱う。
これらの共有ファイルは編集していない。既に終了した実行を再起動していない。

### 次の独立した主工程：pねじれ係数への一元分冪代数の基底変更

原典Lemma 2.43（著者版26–27頁）のmod p計算へ進むには、pねじれ係数も扱える一元分冪代数の
基底変更が必要。今回のRankOneDPBaseChangeEquivはA,Bのp正則性を明示しているため、
B=Fpへの適用やLemma 2.43の導来計算を解決したとは数えない。
既存の一般rankOneDPBaseChangeMapに対し、DividedPowerAlgebra.lift'を使って
γ_n(b)をb^n・(1⊗γ_n(1))へ送る逆射を構成し、積・加法関係を二項展開と既存分冪積公式で確認する。
これにより任意係数Bへの同型を得て、整数係数の既証明基底から任意係数の基底、
mod pでのγ₁(1)のp冪零性と次数ブロック分解へ進む。
新規ファイルは着手時に登録し、共通G3・G6・G7の実装待ちとこの独立工程を区別する。

### 次工程の登録：任意係数への一元分冪テンソル生成元の関係式

BS専用RankOneDPTensorRelations.leanで、任意の可換環Aと可換A代数Bに対し、
b^n⊗γ_n(1)という具体的テンソル族を作る。零次・Bスカラー・同一元の積・加法の
全関係式を、既存分冪積公式と二項展開で証明する。
p正則性・p局所性を要求せず、次の既存DividedPowerAlgebra.lift'による逆射の入力にする。
新しい分冪代数そのものは定義しない。

## B4-6：任意係数への具体的分冪テンソル族の全関係式（2026-10-15）

RankOneDPTensorRelations.leanで、任意の可換環Aと可換A代数Bに対しb^n⊗γ_n(1)の実族を作り、
零次・全Bスカラー・同一元の全積・全加法の関係式を証明した。
加法関係には二項展開のantidiagonal表示と既存分冪積公式を用いた。
p正則性・p局所性・δ構造・完備性は不要。5公開宣言の対象2710ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。逆射の構成・導来比較・CFF・一般B4は次工程。

### 次工程の登録：任意係数への一元分冪代数の実基底変更同型

BS専用RankOneDPBaseChangeUniversal.leanで、既存lift'と前工程の関係式から、
Γ_B(B)→ₐ[B]B⊗[A]Γ_A(A)の実逆射を構成する。生成元上の式と両合成の恒等性を証明し、
既存rankOneDPBaseChangeMapを順射とする実代数同型を公開する。
A,Bのp正則性・p局所性・δ構造・完備性は要求しない。
従来のp正則性を明示した公開APIは削除・変更せず、より一般の比較を新たに供給する。

## B4-6：任意係数への一元分冪代数の実基底変更同型（2026-10-15）

RankOneDPBaseChangeUniversal.leanで、既存lift'に全関係式を渡して実逆射を構成し、
γ_n(b)の像がb^n⊗γ_n(1)であること、順逆両合成の恒等性を証明した。
既存rankOneDPBaseChangeMapを順射とする実代数同型を構成し、全純テンソル上の式を公開した。
任意の可換環Aと可換A代数Bを許し、p正則性・p局所性・δ構造・完備性は要求しない。
従来のp正則性を明示したAPIは変更していない。
8公開宣言の対象2711ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。通常基底変更の結果であり、導来比較・CFF・一般B4は未完成。

### 次工程の登録：任意係数での既存一元分冪代数の実基底

BS専用RankOneDPAnyBasis.leanで、整数係数の既証明基底を任意の可換環Aへテンソル基底変更し、
前工程の無条件の実同型を使ってModule.Basis ℕ A (DividedPowerAlgebra A A)を構成する。
全基底元がγ_n(1)であることと自由性を公開し、既存平坦基底変更補題により
係数環の正則元がこの分冪代数でも正則であることを証明する。
pねじれ・零環を許し、p局所性・p正則性・δ構造・完備性は要求しない。

## B4-6：任意係数での既存一元分冪代数の実基底（2026-10-15）

RankOneDPAnyBasis.leanで、整数係数の既証明基底を任意の可換環Aへテンソル基底変更し、
無条件の実比較同型で移して、全γ_n(1)を基底元とする実Module.Basisを構成した。
任意係数での自由性と、係数環の正則元が分冪代数でも正則であることも既存平坦性補題で証明した。
pねじれ・零環を許し、p局所性・p正則性・δ構造・完備性は不要。
4公開宣言の対象2712ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。mod p次数ブロック分解、導来比較、CFF、一般B4は未完成。

### 次工程の登録：p=0の係数環での一元分冪基底の次数ブロック計算

BS専用RankOneDPPrimeBlocks.leanで、(p:A)=0を明示し、一次生成元x=γ₁(1)について
x・γ_(pk+r)=(r+1)γ_(pk+r+1)、x^r・γ_(pk)=r!γ_(pk+r)を証明する。
任意のrを許し、正のpに対しx^p=0も導く。非零環・CharP・p正則性は仮定しない。
これはmod pでの切断多項式作用と自由ブロック分解の具体的入力であり、
まだ切断多項式環上の自由性や導来比較・CFFを主張しない。

## B4-6：p=0の係数環での次数ブロック作用の具体式（2026-10-15）

RankOneDPPrimeBlocks.leanで、一次生成元xの標準基底への積公式を証明した。
(p:A)=0の下でx・γ_(pk+r)=(r+1)γ_(pk+r+1)、x^r・γ_(pk)=r!γ_(pk+r)を任意rに対して公開し、
正のpについてx^p=0も導いた。非零環・CharP・p正則性を仮定しない。
4公開定理の対象2713ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。切断多項式環上の自由ブロック分解・導来比較・CFF・一般B4は未完成。

### 次工程の登録：p=0の係数環での実次数ブロック基底

BS専用RankOneDPPrimeBlockBasis.leanで、p素数と(p:A)=0の下、r<pのr!の単元性を
既存Coprime.castとBézout判定から供給する。任意係数の実基底をNat.divModEquiv pで
ℕ×Fin pへ付け替え、階乗で拡大して、基底元x^rγ_(pk)を持つ実A加群基底を構成する。
さらにx倍がブロック内で次の元へ進み、最後の元を零へ送る式を公開する。
零環を許し、これはA加群の実ブロック基底である。切断多項式環上の自由性は別工程。

## B4-6：p=0の係数環での実次数ブロック基底（2026-10-15）

RankOneDPPrimeBlockBasis.leanで、p素数・(p:A)=0の下、r<pのr!の単元性を
既存Coprime.castとBézout判定から供給した。
任意係数の実基底をNat.divModEquiv pでℕ×Fin pへ付け替え、階乗で拡大して
(k,r)↦x^rγ_(pk)を基底元とする実A加群基底を構成した。
x倍がブロック内部で次の基底元へ進み、最後の基底元を零へ送ることも公開した。
零環を許し、非零性・CharPインスタンス・p局所性は要求しない。
5公開宣言の対象2715ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。

次の主要工程は、この実A基底とxの作用を、実切断多項式環A[X]/(X^p)の
標準冪基底へ接続し、同環上でγ_(pk)を基底とする自由性を証明することである。
現段階はA加群の実ブロック基底であり、切断多項式環上の自由性・原典Lemma 2.43の
導来基底変更・完全平坦性・CFF・一般B4を完了したとは数えない。
任意係数への基底変更と任意係数の実基底の到着により、前回不足していた
mod pのpねじれ係数を扱う通常代数の入力は得られた。共通G3・G6・G7は別の待合せ。

### 次工程の登録：実切断多項式環の作用と標準冪基底

BS専用RankOneDPTruncatedAction.leanで、実環AdjoinRoot ((X:A[X])^p)から
既存一元分冪代数への射を、根をγ₁(1)へ送るAdjoinRoot.liftAlgHomで作る。
(p:A)=0と0<pによる既証明の冪零性を使い、係数可換性と実スカラー塔を供給する。
係数環が非零の場合には既存AdjoinRoot.powerBasis'をFin pへ付け替え、
根のr乗が基底であることと、その作用像がγ₁(1)^rであることを証明する。
非零性はこの冪基底の中間補題に限り、後続の自由性定理では零環の場合を別途扱う。

## B4-6：実切断多項式環の作用と標準冪基底（2026-10-15）

RankOneDPTruncatedAction.leanで、AdjoinRoot ((X:A[X])^p)の根を一次分冪生成元へ送る
実A代数射を構成した。(p:A)=0と0<pから既証明の冪零性を供給した。
この実射によるスカラー作用、元のA作用との実スカラー塔、根の像を公開した。
非零係数環について既存powerBasis'をFin pへ付け替え、標準冪基底の値とその作用像を証明した。
この中間冪基底のみ非零性を仮定し、後続の自由性では零環も別途扱う。
7公開宣言の対象2716ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。切断多項式環上の自由性・導来比較・CFF・一般B4は未完成。

### 次工程の登録：実切断多項式環上の自由性と忠実平坦性

BS専用RankOneDPTruncatedFree.leanで、p素数・(p:A)=0の下、実切断多項式環T=AdjoinRoot(X^p)の
既定の作用について、ℕ→₀TからΓ_A(A)への線形結合写像を作る。
非零Aの場合は標準冪基底を持つ有限台係数族のA基底と既存実ブロック基底を照合し、
このC線形写像の全単射性を証明する。零Aの場合は元・係数両側が零であることから扱う。
実T線形同値とγ_(pk)を基底とする実T基底を構成し、自由性・平坦性・忠実平坦性を公開する。
非零性・Noetherian性・完備性を最終の通常加群定理の仮定へ追加しない。
これは原典Lemma 2.43のmod p計算の通常一元入力であり、導来比較・CFFとは区別する。

## B4-6：実切断多項式環上の自由性・忠実平坦性（2026-10-15）

RankOneDPTruncatedFree.leanで、p素数・(p:A)=0の下、既定の実作用について
(ℕ→₀AdjoinRoot(X^p))→Γ_A(A)の実線形結合写像を構成した。
標準冪基底を持つ係数族のA基底と既存実ブロック基底を照合し、全単射性を証明した。
零Aの場合も別途扱い、非零性の仮定は最終結果に追加していない。
実線形同値、一項係数族上の式、γ_(pk)を基底元とする実切断多項式環上の基底を公開し、
既存Module.FreeとModule.FaithfullyFlatのAPIで自由性・平坦性・忠実平坦性を証明した。
Noetherian性・完備性・δ構造は不要。10公開宣言の対象2718ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。
これは原典Lemma 2.43のmod pにおける通常一元加群の自由性を供給する成果である。
原典の導来pushout比較・Koszulとの導来基底変更・完備化後の完全平坦性・CFF・一般B4は未完成。

### 次工程の登録：多項式作用と切断多項式作用の実因子化

BS専用RankOneDPPolynomialAction.leanで、A[X]の変数をγ₁(1)へ送る既存aevalによる実A代数射、
その具体的スカラー作用、係数とのスカラー塔を公開する。
AdjoinRoot(X^p)に対しては実商写像mkによるA[X]代数構造を明示し、
既存の切断多項式作用との合成が元の多項式作用に一致することと実スカラー塔を証明する。
後続の通常テンソル・Tor比較で非自明な多項式作用を恒等作用と取り違えないための入力である。
一般の導来テンソル・完全平坦性の新定義は作らない。

## B4-6：多項式作用と実切断多項式作用の因子化（2026-10-15）

RankOneDPPolynomialAction.leanで、変数をγ₁(1)へ送る実aeval、具体的な多項式スカラー作用、
係数との実スカラー塔を公開した。
AdjoinRoot(X^p)について実商写像mkの多項式環上の作用を明示し、切断多項式作用との
合成が元の多項式射に一致することと、三環の実スカラー塔を証明した。
後続のテンソル・Torで使う非自明な多項式作用を、恒等作用や未指定の作用と混同しない。
9公開宣言の対象2719ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。導来比較・完備化後の完全平坦性・CFF・一般B4は未完成。
共通計画ではG3・G6・G7は引き続き未完了であり、この成果には使用していない。

### 次の独立した主工程：通常分冪添加環への実基底変更

Aをp=0の可換環、Bを可換A代数、y:Bとし、P=A[X]の作用をBにはX↦y、
Γ_A(A)にはX↦γ₁(1)として明示する。
C=AdjoinRoot(X^p)、U=C⊗[P]B、D=Γ_A(A)⊗[P]Bを実際の環として作る。
既存テンソルの交換・cancelBaseChangeでU⊗[C]Γ_A(A)≃Dを構成し、
U→Dの実環射に関する自由性・忠実平坦性を、今回のC上の自由性の基底変更で得る。
続いて既存テンソル商同型でU≃B/(y^p)を同定し、B/(y^p)がA平坦ならDがA平坦であることへ接続する。
新規ファイルは着手時に登録する。この通常計算と、原典の導来pushout・Koszul比較は分ける。

### 次工程の登録：通常分冪添加の実テンソル基底変更

BS専用RankOneDPEnvelopeBaseChange.leanで、P=A[X]の指定された任意のBへの環射を
Algebra P Bとして明示し、C=AdjoinRoot(X^p)、U=C⊗[P]B、D=Γ_A(A)⊗[P]Bを実際の環として扱う。
Γ_A(A)とCへのP作用には既存の指定された実作用を使用する。
(p:A)=0、0<pの下でU→Dの実比較射、U⊗[C]Γ_A(A)≃Dの実同型を構成し、
全純テンソル上の式を確認する。さらにこの同型をU代数同型へ持ち上げる。
BへのP作用の変数の像をyとすれば、後続でUをB/(y^p)へ同定できる。
導来pushout・Torの一般基盤は新設しない。

## B4-6：通常分冪添加環への実テンソル基底変更（2026-10-15）

RankOneDPEnvelopeBaseChange.leanで、指定されたAlgebra (Polynomial A) Bについて、
C=AdjoinRoot(X^p)、U=C⊗[A[X]]B、D=Γ_A(A)⊗[A[X]]Bを実環として固定した。
(p:A)=0・0<pの下、既存切断多項式作用の基底変更による実射U→Dと、
U⊗[C]Γ_A(A)≃Dの実C代数同型を構成し、全生成純テンソル上の式を証明した。
さらに同型がUの標準射を指定された実射へ送ることを確認し、その実U作用を保つU代数同型へ持ち上げた。
9公開宣言の対象2720ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。自由性の基底変更・商への同定・導来比較・CFF・一般B4は次工程。

### 次工程の登録：基底変更後の通常分冪添加環の自由性・忠実平坦性

BS専用RankOneDPEnvelopeFree.leanで、p素数・(p:A)=0と指定されたA[X]代数Bについて、
実比較射U→Dの作用に関する実U基底を既存の切断多項式環上の基底の基底変更で構成する。
基底元γ_(pk)⊗1の式、Module.Free・Module.Flat・Module.FaithfullyFlatを公開する。
Bやy=変数の像の正則性・有限性・非零性は要求せず、通常加群の結果に限定する。

### 次工程の登録：基底変更した切断多項式環と実商の同定

BS専用RankOneDPTruncationQuotient.leanで、指定されたAlgebra (Polynomial A) Bに対し、
y=algebraMap (Polynomial A) B Xとして、B/(y^p)≃C⊗[A[X]]Bを構成する。
実テンソル商同型と商イデアルの像の一致を使用し、Bの全代表元とyの像上の式を公開する。
pの素数性・(p:A)=0・正則性・完備性はこの通常商の同定に要求しない。

## B4-6：基底変更後の通常分冪添加環の自由性・忠実平坦性（2026-10-15）

RankOneDPEnvelopeFree.leanで、p素数・(p:A)=0の下、実射U→Dに関する実U基底を
切断多項式環上の既存基底の基底変更と実同型で構成した。
各基底元がγ_(pk)⊗1であること、自由性・平坦性・忠実平坦性を公開した。
Bの正則性・変数の像の正則性・有限性・非零性・完備性は要求しない。
5公開宣言の対象2721ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。実商B/(y^p)との同定、導来比較、CFF、一般B4は未完成。

## B4-6：基底変更した実切断多項式環とB/(y^p)の同定（2026-10-15）

RankOneDPTruncationQuotient.leanで、指定されたA[X]代数Bについて、
y=algebraMap A[X] B Xとし、B/(y^p)≃C⊗[A[X]]Bの実環同型を構成した。
X^pの主イデアルの像の一致を確認し、既存テンソル商同型と交換同型を使用した。
全代表元の像、商のyと実切断多項式環の根の対応も公開した。
pの素数性・(p:A)=0・正則性・完備性は不要。
4公開宣言の対象2721ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。商から分冪添加環への実射・導来比較・CFF・一般B4は次工程。

### 次工程の登録：実商B/(y^p)から通常分冪添加環への自由・忠実平坦な実射

BS専用RankOneDPQuotientToEnvelope.leanで、実商同型B/(y^p)≃Uと実比較射U→Dを合成し、
商から通常分冪添加環への実環射を構成する。全代表元の像が1⊗bであることを示す。
p素数・(p:A)=0の下、指定した実射に関する自由性・平坦性・忠実平坦性を
既存の同型・基底のスカラー塔・忠実平坦性の推移律で導く。
零環を許し、yの正則性・Noetherian性・完備性は要求しない。
原典の導来比較や完備化後のCFFそのものとは区別する。

### 次工程の登録：通常分冪添加環の係数環上の平坦性

BS専用RankOneDPEnvelopeCoefficientFlat.leanで、指定されたA[X]代数Bから誘導される
A→B/(y^p)とA→Dの実係数射を明示する。
実射B/(y^p)→Dとの可換性をテンソルの釣合い式で証明し、対応する実スカラー塔を供給する。
p素数・(p:A)=0の下、既存平坦性の推移律により、B/(y^p)がA平坦ならDがA平坦であることを公開する。
通常テンソル環の条件付き平坦性であり、導来pushoutの離散性や完備化後の完全平坦性とは分ける。

## B4-6：実商B/(y^p)から通常分冪添加環への自由・忠実平坦な実射（2026-10-15）

RankOneDPQuotientToEnvelope.leanで、実商同型と指定された実比較射を合成して
B/(y^p)→Dを構成し、全代表元bの像が1⊗bであることを証明した。
この実射による商環上の作用と、商からUを経由する実スカラー塔を明示した。
p素数・(p:A)=0の下、既存の実基底とスカラー塔の基底の合成、忠実平坦性の推移律を使い、
この実射に関するModule.Free・Module.Flat・Module.FaithfullyFlatを証明した。
零環を許し、yの正則性・Noetherian性・完備性は不要。
8公開宣言の対象2723ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。導来pushout比較・完備化後の完全平坦性・CFF・一般B4は未完成。

## B4-6：通常分冪添加環の実係数射と係数環上の平坦性（2026-10-15）

RankOneDPEnvelopeCoefficientFlat.leanで、指定されたA[X]代数BからA→B/(y^p)とA→Dの
実係数射を明示し、商から分冪添加環への実射との可換性をテンソルの釣合い式で証明した。
対応する実スカラー塔を構成し、p素数・(p:A)=0の下、B/(y^p)が指定した係数作用について
A平坦なら通常テンソル環DもA平坦であることを、既存Module.Flat.transで証明した。
DのA加群構造には既存テンソルの自然な左係数作用を用い、補助的なtoAlgebraの作用へ
無条件に置き換えていない。係数射の一致を確認して自然作用上のスカラー塔を供給した。
零環を許し、正則性・Noetherian性・完備性の仮定は追加していない。
7公開宣言の対象2724ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。原典の導来pushoutとの比較・離散性・完備化後の完全平坦性・CFF・一般B4は未完成。

### 次の接続工程

指定されたA[X]代数という一般入口を、元の可換A代数Bとy:BについてX↦yの評価作用へ
特殊化し、既存の自然な商A加群構造での平坦性仮定と接続する。
商の自然作用と誘導係数作用が定義上同一とは仮定せず、必要なスカラー塔を実射で確認する。
さらに任意係数の既証明一元分冪代数の基底変更を用い、従来p正則係数に限定していた
PrincipalDPPresentationの基底変更をpねじれ係数にも拡張する。
これらの通常比較を、原典の導来テンソル・Koszul比較や未受領の共通G3・G6・G7の解消とは数えない。

### 次工程の登録：具体的A代数Bと元yへの評価入口

BS専用RankOneDPEvaluatedEnvelope.leanで、既存の可換A代数Bと元y:Bを入力とし、
Polynomial.aeval yによるA[X]作用を明示する。
B/(y^p)から評価作用で作った通常テンソル環への実射を構成し、全代表元の式と忠実平坦性を公開する。
自然な商A加群構造と自然な左係数作用を保つ実スカラー塔を直接証明し、
Module.Flat A (B/(y^p))から評価された通常添加環のModule.Flatを導く。
既存のA代数構造や商の作用を補助的なtoAlgebraへ無条件に差し替えない。
新規引用・導来圏の新定義は作らず、通常比較と導来比較を分ける。

### 次工程の登録：一元分冪表示環の任意係数への基底変更

BS専用PrincipalDPBaseChangeUniversal.leanで、任意係数の既証明一元分冪代数同型を使い、
B⊗[A]PrincipalDPPresentation A y≃ₐ[B]PrincipalDPPresentation B (algebraMap A B y)
をp正則性・p局所性なしで構成する。既存の表示関係の像の計算とテンソル商同型を再利用し、
Bの係数と全標準生成元上の式を公開する。従来の仮定付き公開APIは変更しない。
この一般比較はpねじれ係数へのmod p比較に使用する。

## B4-6：具体的A代数Bと元yへの評価入口（2026-10-15）

RankOneDPEvaluatedEnvelope.leanで、元の可換A代数Bと指定元y:Bについてaeval yによる
多項式作用と、通常の実評価テンソル環を定義した。
B/(y^p)から実評価環への射を構成し、すべての商代表元bの像が1⊗bであることを証明した。
p素数・(p:A)=0の下、この実射の通常の忠実平坦性を、実イデアル同型と既存の結果から移した。
さらに元のA作用、自然な商A加群構造、自然な左係数作用についてスカラー塔を直接証明し、
自然なModule.Flat A (B/(y^p))から実評価テンソル環のModule.Flatを導いた。
自然な商作用を補助的なtoAlgebraの作用へ無条件に差し替えていない。
10公開宣言の対象2725ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。原典の導来pushoutとの比較・完備化後の完全平坦性・CFF・一般B4は未完成。

### 次工程の登録：一元分冪表示環の実mod p比較

BS専用PrincipalDPModP.leanで、PrincipalDPPresentation A yを実際にpで割った商を、
PrincipalDPPresentation (A/p) (y mod p)へ同定する。
係数のp主イデアルの像、既存テンソル商同型、任意係数の基底変更同型を合成し、
係数と全標準生成元上の式を証明する。pねじれ・零環を許し、pの素数性・p正則性・
完備性は要求しない。この通常mod p同型を導来完備化の比較と混同しない。

## B4-6：一元分冪表示環の任意係数への実基底変更（2026-10-15）

PrincipalDPBaseChangeUniversal.leanで、既証明の任意係数の一元分冪代数同型を使い、
拡大した表示関係イデアルの像の一致を証明した。
既存テンソル商同型と合成し、B⊗[A]PrincipalDPPresentation A yから
PrincipalDPPresentation B (algebraMap A B y)への実B代数同型を構成した。
Bの全係数・全標準生成元の純テンソル上の式も公開した。
p正則性・p局所性・δ構造・完備性は不要で、pねじれ係数を許す。従来の仮定付きAPIは変更していない。
4公開宣言の対象2714ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。実mod p比較・導来比較・CFF・一般B4は次工程。

### 次工程の登録：正則一元階乗部分環の実mod p比較

BS専用RegularPrincipalDPModP.leanで、p局所・p正則なδ環Aとy mod p正則性を明示し、
既存の実表示環同型をp商へ降ろして、具体的階乗部分環のp商を
PrincipalDPPresentation (A/p) (y mod p)へ同定する。
基底射の全係数と全階乗生成元の商像上の式を公開する。
これはB4の具体的通常環のmod p比較であり、原典の導来pushout比較や完備化比較は別工程。

## B4-6：一元分冪表示環の実mod p比較（2026-10-15）

PrincipalDPModP.leanで、係数のp主イデアルの像の一致、既存テンソル商同型、
任意係数の実基底変更を合成し、表示環を実際にpで割った商を
PrincipalDPPresentation (A/p) (y mod p)へ同定した。
全係数と全標準生成元の商像上の式も証明した。pねじれ・零環を許し、
pの素数性・p正則性・δ構造・完備性は要求しない。
4公開宣言の対象2715ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。これは通常のp商の同型であり、導来完備化・古典的完備化の比較ではない。

### 全体ビルドの検証境界（今回の実行）

前回開始した全体lake buildを同じ実行ハンドルで継続観測し、終了コード1を確認した。
ログは /tmp/bs-dpenvelopequotient-full-build.log。
共有KTheory/Adams/WeightAnnihilation.lean:1でPerfectComplex/IntegerEuler.oleanの欠落が報告された。
この全体検証の失敗を、今回のBS対象ビルド・B4全体pure監査の成功と区別する。
共有ファイルは編集せず、観測のタイムアウトを理由に実行を再起動していない。

## B4-6：正則一元階乗部分環の実mod p比較（2026-10-15）

RegularPrincipalDPModP.leanで、p局所・p正則なδ環とy mod p正則性の下、
既存の実表示環同型をp商へ降ろした。具体的階乗部分環のp商から
PrincipalDPPresentation (A/p) (y mod p)への実環同型と、全係数・全階乗生成元上の式を証明した。
4公開宣言の対象2746ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。通常の商環の比較であり、導来pushout・完備化比較・CFF・一般B4は未完成。

### 次工程の登録：係数環自身への評価テンソル比較

BS専用PrincipalDPEvaluationTensor.leanを追加し、Γ_A(A)⊗[A[X]]A（Xをyへ評価）と
PrincipalDPPresentation A yを実環同型で比較する。既存の多項式一次商同型・テンソル商同型を再利用し、
係数・分冪生成元上の式を証明する。pの仮定を置かない通常環の比較を最初の単位とする。

## B4-6：表示環と実評価テンソル環の比較（2026-10-15）

PrincipalDPEvaluationTensor.leanで、既存の多項式一次商同型とテンソル商同型を合成した。
任意の可換環Aとy:Aについて、PrincipalDPPresentation A yとΓ_A(A)⊗[A[X]]Aの
実環同型および元の係数作用を保つA代数同型を証明した。
全商代表元・全標準生成元・全係数の像も公開した。p正則性・標数・完備性は不要。
7公開宣言の対象2727ジョブ成功。依存監査結果は後記する。

### 次工程の登録：標数pでの表示環の忠実平坦性

BS専用PrincipalDPQuotientFlat.leanで、p素数・(p:B)=0の下、任意のy:Bに対し
B/(y^p)からPrincipalDPPresentation B yへの実射とその忠実平坦性を構成する。
既存の評価テンソル環の忠実平坦性を実同型で移し、基底環A上のB/(y^p)の通常平坦性から
表示環の通常平坦性を導く。導来pushout比較・完備化後の完全平坦性はこの工程には含めない。

実評価テンソル比較7公開宣言のB4全体pure監査も成功。標準3公理のみ。新sorry・公理・引用なし。

## B4-6：標数pでの表示環の忠実平坦性（2026-10-15）

PrincipalDPQuotientFlat.leanで、p素数・(p:B)=0の下、任意のy:Bについて
B/(y^p)からPrincipalDPPresentation B yへの実射を構成した。全代表元bの像は自然な係数b。
実評価テンソル同型がこの商上の代数同型でもあることを示し、忠実平坦性を移した。
任意の基底環A上の自然な商加群B/(y^p)が平坦なら、表示環もA平坦と証明した。
B自体のA平坦性・yの正則性・非零性・完備性は不要。自然なA作用との実スカラー塔を証明している。
8公開宣言の対象2728ジョブ成功。通常平坦性であり導来比較・CFF・一般B4は未完成。

### 次工程の登録：正則階乗部分環のmod p平坦性判定

BS専用RegularPrincipalDPModPFlat.leanで、p局所・p正則なδ環Aとy mod p正則性の下、
具体的階乗部分環のp商のA/p作用を構成し、全係数上で元の基底射と一致することを証明する。
任意の基底環K→A/pに対し、(A/p)/((y mod p)^p)のK平坦性から、
この実p商のK平坦性を導く。Frobeniusによる係数作用にも利用できる形にし、
その通常平坦性をG3の完全平坦性判定の入力候補とする。G3や導来pushout比較そのものは主張しない。

表示環の商上平坦性8公開宣言のB4全体pure監査も成功。標準3公理のみ。新sorry・公理・引用なし。

## B4-6：正則階乗部分環のmod p通常平坦性判定（2026-10-15）

RegularPrincipalDPModPFlat.leanで、p局所・p正則なδ環Aとy mod p正則性の下、
具体的階乗部分環のp商にA/p作用を指定し、全係数上で元の基底射のp商と一致することを証明した。
実比較をA/p代数同型に強め、任意のK→A/p作用について、
(A/p)/((y mod p)^p)のK平坦性から実階乗部分環のp商のK平坦性を証明した。
K作用の合成とスカラー塔を明示している。Frobenius作用にも適用できるが、その作用での
商の平坦性を無条件に主張していない。4公開宣言の対象2762ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。G3・導来pushout比較・完備化比較・一般B4は未完成。

### 次工程の登録：切断多項式商の実導来Koszul比較

BS専用RankOneDPTruncationDerived.leanで、既存のDerivedQuotientKoszulを再利用し、
多項式X^pの正則性から、P/(X^p)への実導来係数拡大をP上へ制限した対象と
実導来Koszul coneとの比較を公開する。具体的なA代数BへのX↦yの評価に特殊化し、
X^pの作用がy^pであること・作用の正則性の一致を証明する。
これはLemma 2.43の切断多項式側の導来成分であり、Γとの全導来pushout比較や完備化比較を完了とはしない。

## B4-6：切断多項式側の実導来Koszul比較（2026-10-15）

RankOneDPTruncationDerived.leanで、任意の可換係数環（零環も含む）のX^pの正則性を証明した。
既存のDerivedQuotientKoszulを再利用し、P/(X^p)への実導来係数拡大をP上へ制限した対象と
実導来Koszul coneの比較を、任意の上有界導来対象に対して公開した。
具体的なA代数BへのX↦yの評価・次数零対象にも適用し、X^pの作用とy^pの作用、
両作用の正則性が一致することを証明した。通常商への置換や完備性は仮定していない。
5公開宣言の対象3130ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。Lemma 2.43の切断多項式側の導来成分であり、
分冪代数全体との導来pushout比較・相対Koszul平坦性・完備化比較・CFFは引き続き未完成。

### 次の接続点と未完了工程

通常環では、評価テンソル同型→表示環のp乗商上の忠実平坦性→正則階乗部分環の実mod p平坦性判定まで接続した。
導来側では、切断多項式商を実Koszul coneで計算する入口を供給した。
次は分冪代数の切断多項式環上の具体的自由加群構造を、この導来比較に接続する。
一般の相対入力で通常商をKoszulの代わりに用いるには、その入力での比較の証明が必要。
G3の完全平坦性判定、G6のJacobson判定、G7の逐次Tor移送は共通側の公開APIを待つ工程として保持する。
今回も既存André引用には依存していない。必要な完全忠実平坦根付き拡大の引用なし構成と一般B4は未完成。

### 次工程の登録：分冪代数への実導来係数拡大の因子化

BS専用RankOneDPDerivedFactorization.leanで、P=A[X]→C=P/(X^p)→Γ_A(A)の
既存の実射・合成図式と、既存の射影モデル・baseChangeCompIsoを再利用し、
P→Γへの実導来係数拡大を二段階の実導来係数拡大に同定する。
p素数・(p:A)=0の下で既証明のC上自由性からC→Γの忠実平坦性を環射の形で供給し、
C→Γの実導来拡大を通常の平坦な導来関手へ同定する。
可能な範囲で全次数ホモロジーの比較・零性反映を公開する。
一般の導来係数拡大合成APIは新設せず、既存共通モデルのBS実射への適用として実装する。

## B4-6：分冪代数への実導来係数拡大の因子化（2026-10-15）

RankOneDPDerivedFactorization.leanで、既存の射影モデルと複体の係数拡大合成同型を使い、
実射P=A[X]→C=P/(X^p)→Γ_A(A)について、P→Γの実導来係数拡大を二段階に同定した。
p素数・(p:A)=0の下、既証明のC上自由性から実C→Γ射の忠実平坦性を環射の形で供給し、
後半の実導来拡大を平坦拡大に同定した。全次数ホモロジーの通常係数拡大による計算と
各ホモロジーの零性の反映を証明した。零環・一般の上有界導来対象を含む。
6公開宣言の対象3181ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。共有LocalFlatnessCriterionの既存長行警告は今回のBS変更と区別する。
一般の導来係数拡大合成の定義は重複させていない。

### 次工程の登録：分冪代数の導来Koszul判定

BS専用RankOneDPDerivedKoszul.leanで、Cへの実導来拡大のホモロジーをP上へ制限し、
既存のKoszul同型と比較する。上の忠実平坦因子化と結び、Γへの実導来拡大の
各ホモロジーの零性をX^pの実導来Koszul coneの零性と同値にする。
次数零加群については既存のTor比較により全高次Tor消滅の具体的Koszul判定へ移し、
その仮定を明示した場合のみ標準augmentationによる通常テンソルとの同型を公開する。
導来完備化を古典的完備化へ置換する工程とは区別する。

## B4-6：実分冪導来拡大のKoszul判定（2026-10-15）

RankOneDPDerivedKoszul.leanで、切断多項式側の実導来ホモロジーをPへ制限した加群と
X^pの実Koszul coneのホモロジーとの同型を証明した。
忠実平坦因子化により、Γへの実導来拡大の各ホモロジーの零性がこのKoszulホモロジーの零性と同値になった。
次数零加群では、既存の実Tor比較を再利用し、全高次Tor消滅のKoszul判定を公開した。
その消滅条件を明示した場合のみ、既存標準augmentationによる通常テンソルへの比較同型を構成した。
4公開宣言の対象3183ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。導来対象を通常商へ無条件に置換していない。

### 次工程の登録：切断多項式作用による分冪テンソルの相対平坦性

BS専用RankOneDPTruncatedTensorFlat.leanで、p素数・(p:A)=0の下、C=A[X]/(X^p)の
任意加群Mについて、Γ_A(A)⊗[C]Mをℕ→₀Mへ具体的なA線形同値で同定する。
既存のΓのC自由基底とMathlibのFinsuppテンソル同型を再利用する。
元のA作用・C作用のスカラー塔を明示し、MのA平坦性とこの実テンソルのA平坦性の同値を証明する。
これを実導来ホモロジー比較に適用する工程は、型が確定し次第続ける。

### 次工程の登録：実導来ホモロジーの相対平坦性判定

BS専用RankOneDPDerivedRelativeFlat.leanで、係数作用をModuleCat.restrictScalarsで明示し、
C→Γに沿う実係数拡大のA平坦性が元のC加群のA平坦性と同値になることを証明する。
これを実導来ホモロジー同型と合成し、Γへの実導来拡大の各ホモロジーのA平坦性を
切断多項式側へ移す。P上の実Koszulホモロジーとの比較も、A線形性を保って接続する。
新しい一般の平坦性・Tor・導来係数拡大の定義は作らない。

## B4-6：切断多項式作用による実分冪テンソルの相対平坦性（2026-10-15）

RankOneDPTruncatedTensorFlat.leanで、C=A[X]/(X^p)の任意加群Mについて、
Γ_A(A)⊗[C]Mをℕ→₀Mへ、元のA作用を保つ実線形同値で同定した。
γ_(pk)⊗mが第k成分だけmの係数族へ写る式を証明した。
既存Finsupp・直和の平坦性を再利用し、実テンソルのA平坦性とMのA平坦性の同値を得た。
3公開宣言の対象2719ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。導来ホモロジーへは次工程で係数制限の作用を照合して適用する。

### 次工程の登録：具体的評価環の導来比較とKoszul平坦性

BS専用RankOneDPEvaluatedDerivedFlat.leanで、具体的A代数B・元yについて、
X↦yで定まるP作用の実導来Γ係数拡大と既存RankOneDPEvaluatedEnvelope A B yを比較する。
標準H0比較を元のA作用と整合させ、実評価環のA平坦性をX^pの実Koszul H0のA平坦性に同定する。
実Koszulの全負次ホモロジー消滅を仮定した場合のみ、標準augmentationによる
実導来拡大全体と通常評価環の次数零対象の同型を公開する。
完備化・混標数・複数変数・一般の導来代数に関する追加工程は未完了として区別する。

## B4-6：実導来ホモロジーの相対平坦性判定（2026-10-15）

RankOneDPDerivedRelativeFlat.leanで、C→Γへの実係数拡大をAへ制限した加群と
元のC加群のA制限の可算直和との線形同値を証明した。
係数制限による作用と通常テンソルの左作用の一致はテンソル元上で証明し、作用を無条件に差し替えていない。
これにより実係数拡大のA平坦性の保存・反映を示した。
実導来ホモロジー同型とA線形なKoszul比較を合成し、Γへの実導来拡大の各次数ホモロジーのA平坦性が
X^pの実KoszulホモロジーのA平坦性と同値であることを証明した。
5公開宣言の対象3185ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。完備化と混標数の比較は未完了。

## B4-6：具体的評価環の実導来比較とKoszul平坦性（2026-10-15）

RankOneDPEvaluatedDerivedFlat.leanで、任意の具体的A代数B・元yについて、X↦yの評価作用を指定した。
P→Γへの実係数拡大をAへ制限した加群と、既存の通常評価環とのA線形同値を構成した。
元のA作用と係数制限の作用は純テンソル上で証明して照合した。
既存の標準H0比較と合成し、実導来拡大のH0と通常評価環のA線形同値を得た。
p素数・(p:A)=0の下、通常評価環のA平坦性は実X^p Koszul H0のA平坦性と同値。
さらに実Koszulの全負次ホモロジー消滅を仮定した場合のみ、標準augmentationによる
実導来拡大全体から通常評価環の次数零対象への同型を公開した。
4公開宣言の対象3186ジョブ・B4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。今回の5モジュール22公開宣言はすべて専用監査へ登録済み。

### 現在の検証境界と次の工程

標数p・一元の未完備な実加群導来拡大については、切断多項式因子化、各ホモロジーの零性と
A平坦性のKoszul判定、具体的評価環の標準H0比較・消滅条件付きの全体比較まで接続した。
原典Lemma 2.43全体（導来p完備pushout・複数変数・必要な一般入力）を完成と数えない。
次は標数pでの実導来完備化との比較、および混標数正則入力の実mod p導来比較を既存共通APIで確認する。
G3・G6・G7の未受領はそれらを使う工程に限って保持し、独立したBS比較は続行する。
必要な完全忠実平坦根付き拡大の引用なし構成、一般B4の全射性、B-S引用解消は未完成。

### 次工程の登録：標数pの実分冪導来拡大の完備化比較

BS専用RankOneDPCharacteristicCompletion.leanで、(p:A)=0からΓ_A(A)上のp作用が零となることを用い、
既存のisComplete_of_scalar_pow_zero・標準完備化単位の再構成定理を適用する。
P→Γへの実導来拡大の実p導来完備化と元の導来対象を標準単位で同定し、
各ホモロジーの零性・A平坦性のKoszul判定をこの完備化対象へ移す。
具体的評価代数ではKoszul負次消滅を明示した場合の通常評価環との比較まで接続する。
標数pのみの完備化比較であり、混標数の導来完備化を古典的完備化へ置換する主張は含めない。

## B4-6：標数pの実分冪導来完備化比較（2026-10-15）

RankOneDPCharacteristicCompletion.leanで、(p:A)=0から実Γ導来拡大上のp作用が零となることを用い、
既存の実導来完備性判定と標準完備化単位の再構成定理を適用した。
実p導来完備化と元の導来拡大を標準単位の逆で同定し、各次数の零性とA平坦性の
実Koszul判定を完備化後にも移した。具体的評価環では実Koszul負次消滅を明示した場合の
通常評価環との比較まで接続した。6公開宣言の対象3187ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。標数pのみであり混標数の古典的完備化置換ではない。

### 次工程の登録：正則分冪表示環の実導来完備化のmod p比較

BS専用PrincipalDPCompletionModP.leanで、具体的表示環R=PrincipalDPPresentation A yの
次数零単位加群に対するR上の実導来p完備化を、R→R/pで実導来係数拡大する。
p局所・p正則なAとy mod p正則性から既証明のRのp正則性を供給し、
既存の標準完備化単位の商比較と通常係数拡大の標準augmentationを合成して、
この実対象をR/pの次数零対象に同定する。既存実mod p表示環同型も接続する。
R自身上の単位加群のTor消滅は射影性から証明し、A上のRの平坦性・Tor消滅を仮定しない。
これはR上の導来完備化とその実p商の比較であり、A上への制限との完備化比較や古典的完備化同定は別工程。

### 次工程の登録：元の係数環上の正則表示環のp Koszul比較

BS専用PrincipalDPRelativeModPKoszul.leanで、R=PrincipalDPPresentation A yの列
0→R --p→R→R/p→0を元のA加群の短完全列として証明する。
既証明のRのp正則性、実商射、既存のShortComplexとmappingConeの標準添加写像を再利用する。
そのA上のp Koszul coneからR/pの次数零対象への実擬同型を構成し、
A→A/pへの実導来拡大をAへ制限した対象と結ぶ。
R自身上の単位加群の比較とA上のRの比較を区別し、後者に必要な正則性を明示する。
一般の正則商・Tor・完全平坦性判定を共通層と重複実装しない。

## B4-6：正則分冪表示環上の実導来完備化のmod p比較（2026-10-15）

PrincipalDPCompletionModP.leanで、R=PrincipalDPPresentation A y自身上の単位加群について、
p商への全高次Tor消滅を射影性から証明し、実導来p還元を標準augmentationでR/pの次数零対象へ同定した。
p局所・p正則なAとy mod p正則性を明示し、既証明のRのp正則性と既存標準完備化単位の商比較により、
R上の実導来p完備化の実導来p還元もR/pへ同定した。既存実mod p表示環同型を合成し、
係数A/p上の具体的表示環の次数零対象へも接続した。
p^1=pによる商環・係数圏の変化は、依存する同型型全体の等式移送で明示した。
5公開宣言の対象3152ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
これはR自身上の完備化比較であり、A上のRの平坦性・Tor消滅や、古典的完備化との同定を仮定していない。
元のA上の実比較は別工程として進行中。

### 次工程の登録：元のA→A/pへの実導来表示環比較

BS専用PrincipalDPRelativeDerivedModP.leanで、A上の実Koszul比較と既存のホモロジー・Tor比較から、
p局所・p正則なAとy mod p正則性の下で、R=PrincipalDPPresentation A yの
A→A/pへの全高次Tor消滅を証明する。RのA平坦性は仮定しない。
標準augmentationと既証明の任意係数の表示環基底変更同型を合成し、
A→A/pへの実導来係数拡大をPrincipalDPPresentation (A/p) (y mod p)の次数零対象へ同定する。
G3の完全平坦性判定そのものは共通側の公開APIを待ち、ここでは具体的Tor・導来比較のみを進める。

## B4-6：元の係数環上の正則表示環の実p Koszul比較（2026-10-15）

PrincipalDPRelativeModPKoszul.leanで、具体的表示環Rの列0→R --p→R→R/p→0を
元の係数環A上の短複体として構成し、p局所・p正則なAとy mod p正則性から短完全性を証明した。
A上の実p Koszul coneから実R/pの次数零対象への標準添加写像を構成し、その擬同型性を証明した。
Aのp正則性による既存の実導来商Koszul比較と合成し、A→A/pの実導来還元をAへ制限した対象を
実R/pの次数零対象へ同定した。7公開宣言の対象3135ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。R自身上の単位加群の場合と元のA上の場合を区別している。

### 次工程の登録：元のA上の実導来完備化と具体的mod p表示環

BS専用PrincipalDPRelativeCompletionModP.leanで、A上のRの実導来p完備化を
A→A/pで実導来還元し、係数A/p上の表示環の次数零対象へ同定する。
既存の標準完備化単位の実商比較を適用し、前工程のA上のTor消滅・標準augmentationと合成する。
比較が標準完備化単位と両立することも公開し、古典的完備化への置換は行わない。

## B4-6：元のA→A/pへの実導来表示環比較（2026-10-15）

PrincipalDPRelativeDerivedModP.leanで、p局所・p正則なAとy mod p正則性を公開宣言に明示し、
A上の実Koszul比較からA→A/pへのRの全高次Tor消滅を証明した。RのA平坦性は仮定しない。
既存の実導来ホモロジー・係数制限・Tor比較を再利用し、元のAの作用と商の作用を区別している。
標準augmentationと既存の任意係数の表示環基底変更同型を合成し、
実導来還元をPrincipalDPPresentation (A/p) (y mod p)の次数零対象へ具体的に同定した。
3公開宣言の対象3142ジョブ成功。共通成果物の欠落を受け、B4監査の明示的import対象4231ジョブを再ビルドし成功。
最新依存関係でB4全体pure監査も成功。新規宣言は標準3公理のみ。新sorry・公理・引用なし。
共通ソース・共有監査は編集していない。G3の一般完全平坦性判定は重複実装していない。

## B4-6：元のA上の実導来完備化と具体的mod p表示環（2026-10-15）

PrincipalDPRelativeCompletionModP.leanで、元のAのp正則性を用い、標準A導来完備化単位の
実A→A/p還元が同型となることを既存共通APIから証明した。
これを前工程のA上の実導来表示環比較に合成し、A上のRの実導来p完備化をA→A/pで実導来還元した対象を
係数A/p上の具体的表示環の次数零対象へ同定した。比較は元の標準完備化単位と両立する。
3公開宣言の対象3153ジョブ・最新依存関係でのB4全体pure監査成功。標準3公理のみ。
新sorry・公理・引用なし。通常商・古典的完備化への無条件の置換は行っていない。

### 今回の到達点と残工程

今回5モジュール24公開宣言を、対象ビルドとB4全体pure監査で検証した。
標数pの実導来完備化比較と、混標数正則入力の元のA上の実Tor消滅・実mod p比較・
実導来完備化後のmod p比較を、標準射の両立まで接続した。
この成果をLemma 2.43全体・Corollary 2.44・必要な完全忠実平坦根付き拡大の完成と数えない。
次はこれらの具体的比較をδ除算包側へ接続し、相対正則性と基底変更の入力を供給する。
G3・G6・G7を使う工程のみを待ち、独立したBS比較は続ける。一般B4・B-S引用解消は未完成。

### 次工程の登録：正則raw δ p除算包と分冪表示環の実A代数同型

BS専用DeltaPDivisionRawPrincipal.leanで、Unit添字のraw包A{φ(y)/p}について、
既存のraw包→階乗部分環と表示環→階乗部分環の実同型を合成し、元のA作用を保つ同型を構成する。
p局所・p正則性・y mod p正則性、既存の自由δ環上のWitt ghost単射と指定単元δ(p)を明示する。
全係数と全階乗生成元上の式を証明する。これらの追加仮定を消したとは数えず、
自由δ射の導来pushoutが通常テンソルと一致するという主張も含めない。
共通Witt一般論は再実装せず、共通側の公開APIが来るまでghost単射の仮定を保持する。

raw比較の添字に関する補足：既存の有限段Tor APIの宇宙制約に合わせ、σ:Type uとUnique σを採用する。任意のA:Type uではPUnit.{u+1}が選べる。Unitに固定してAをType 0へ狭めず、定数一元入力の階乗部分環の添字非依存性を証明して既存Unit表示環比較へ接続する。

### 次工程の登録：raw δ p除算包の元のA上の実mod p・完備化比較

BS専用DeltaPDivisionRawRelativeModP.leanで、正則一元raw包B=A{φ(y)/p}の自然なA作用を保つ同型を使い、
既証明の表示環のA→A/p高次Tor消滅と、実導来mod p比較をBへ移す。
A上の実導来完備化後のmod p比較も実関手の同型移送で構成し、標準完備化単位との両立を証明する。
既存のp局所・p正則・mod p正則性、ghost単射と指定単元δ(p)の仮定は明示して保持する。
自由δ環間の射の導来pushoutを通常raw包へ同定したとは数えず、その比較はG7等に関わる別工程とする。

## B4-6：正則raw δ p除算包と分冪表示環の実A代数同型（2026-10-15）

DeltaPDivisionRawPrincipal.leanで、同じType uのUnique σを使う一元raw包A{φ(y)/p}について、
階乗部分環の定数一元入力の添字非依存性を証明し、既存の二つの階乗部分環比較を合成した。
raw包→PrincipalDPPresentation A yの実環同型と、元の自然なA作用を保つA代数同型を構成した。
全係数と全raw階乗生成元上の計算式を公開した。任意Type uでPUnit.{u+1}を選べ、Type 0へ狭めていない。
p局所・p正則・y mod p正則性に加え、既存のghost単射と指定単元δ(p)の仮定は明示して保持する。
5公開宣言の対象3816ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
自由δ射の導来pushout比較・完備化後の完全平坦性を完成と数えない。

### 次工程の登録：実自由δ射の通常テンソルと分冪表示環

BS専用DeltaPDivisionSourcePrincipal.leanで、既存の具体的な自由δ射の通常テンソル
A⊗[A{x}]A{z}（x↦φ(y)、x↦pz）のraw比較を上の実A代数同型へ接続する。
両因子の具体的作用を既存APIから指定し、全純テンソル上の式と係数作用の両立を公開する。
型が確定した場合は、元のA上の実導来完備化と実mod p比較も接続する。
自由δ射の高次Tor消滅を仮定なしに結論せず、通常テンソルと自由δ射の導来テンソルの区別を保持する。

## B4-6：raw δ p除算包の元のA上の実mod p・完備化比較（2026-10-15）

DeltaPDivisionRawRelativeModP.leanで、自然なA作用を保つ実同型からraw包のA→A/p高次Tor消滅を証明した。
A上の実導来mod p対象と、A上の実導来完備化後の実mod p対象を、係数A/p上の
具体的分冪表示環の次数零対象へ同定した。両比較は標準完備化単位と両立する。
4公開宣言の対象3836ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
p局所・p正則性・mod p正則性・ghost単射・指定単元δ(p)の中間仮定は明示して保持した。
自由δ射の導来pushoutを通常raw包へ同定したとは数えない。

### 次工程の登録：raw包の実完備化のp還元ホモロジーと平坦性

BS専用DeltaPDivisionRawResidueFlat.leanで、元のA上のraw包の実導来完備化をA→A/pで導来還元した対象について、
標準ホモロジー関手のH0を具体的表示環へ同定し、全非零次数のホモロジー消滅を公開する。
任意のK→A/p作用に対し、(A/p)/((y mod p)^p)のK平坦性から、この実H0のK平坦性を証明する。
標準同型と既存の標数p分冪表示環の平坦性を再利用し、G3の一般判定や導来pushout比較を重複実装しない。

## B4-6：実自由δ射の通常テンソルと分冪表示環（2026-10-15）

DeltaPDivisionSourcePrincipal.leanで、具体的作用x↦φ(y)、x↦pzによる通常テンソルを
既存raw比較と上の表示環比較により、PrincipalDPPresentation A yへ実環・A代数同型で同定した。
全純テンソルの像を左係数と右因子の実商像で計算する式を公開した。
通常テンソルの元のA上の実導来mod p対象、実導来完備化後のmod p対象も具体的表示環へ接続し、
標準完備化単位との両立を証明した。6公開宣言の対象3849ジョブ・B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。専用監査のimport・宣言登録は直前のraw比較コミットに先行して含まれた。
この実装は通常テンソルに関するもの。自由δ射の高次Tor消滅やその導来テンソルの離散性は未解消。

### 次工程の登録：G7交換入力付きの実自由δ射の導来比較

BS専用DeltaPDivisionSourceDerivedPrincipal.leanで、既存SourceColimitTorの標準PreservesColimit入力を
未解消の仮定として明示し、具体的自由δ射αと評価βの二つのTorを既存の実導来テンソル対称性で比較する。
その入力の下でβに沿う実導来拡大を通常テンソル・具体的表示環の次数零対象へ同定し、
A上の実導来完備化後の実p還元まで接続する。
G7自身の証明や受領とは数えず、無条件の導来δpushout離散性・一般B4完成を主張しない。
一般のTor対称性・colimit交換APIは共通層と重複実装しない。

## B4-6：raw包の実完備化のp還元ホモロジーと相対平坦性（2026-10-15）

DeltaPDivisionRawResidueFlat.leanで、元のA上のraw包の実導来完備化をA→A/pで実導来還元した対象の
H0を具体的表示環へA/p線形同値で同定し、全非零次数の実ホモロジー消滅を証明した。
任意のK→A/p作用について、(A/p)/((y mod p)^p)のK平坦性から、この実H0のK平坦性を導いた。
元の係数作用・QA作用・K作用の塔を明示し、既存の分冪表示環の平坦性を再利用している。
3公開宣言の対象3852ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
中間仮定は保持しており、一般G3や自由δ射の導来pushout比較を完成と数えない。

## B4-6：G7交換入力付きの実自由δ射の導来比較（2026-10-15）

DeltaPDivisionSourceDerivedPrincipal.leanで、具体的α:x↦pzとβ:x↦φ(y)に関する二つのTorを、
既存の実導来テンソル対称性・ホモロジー比較で同定した。
既存SourceColimitTorの標準PreservesColimit入力を各正次数で仮定した場合、βに沿う終域Pの全高次Tor消滅を証明した。
標準augmentationと具体的通常テンソル比較を合成し、実β導来拡大を分冪表示環の次数零対象へ同定した。
元のA上の実p還元・実導来完備化後のp還元も具体的表示環へ接続し、標準完備化単位との両立を公開した。
7公開宣言の対象3857ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
型の推論は具体的係数環Pと中間同型を指定して解決し、このBSファイルのheartbeat上限は増やしていない。
共有LocalFlatnessCriterion・DerivedTensorPentagonの既存警告は今回のBS変更と区別し、共有ソースは編集していない。
これはG7入力に相対的な証明済み成果であり、PreservesColimit自体の実装・受領、G7解消、
無条件の原典導来δpushout比較や一般B4完成とは数えない。既存André引用も使用していない。

## 共通基盤への要求 G8：実導来完備化と係数制限の自然比較（未送信）

対象：任意の可換環R,S:Type u、環射f:R→+*S、a:R、標準加群導来圏上の実対象X。
既存derivedRestrictScalarsとderivedComplexCompletionFunctorを用い、次の自然同型を求める：

    derivedComplexCompletionFunctor S (f a) ⋙ derivedRestrictScalars f
      ≅ derivedRestrictScalars f ⋙ derivedComplexCompletionFunctor R a

標準単位との正確な両立は、自然同型をeとしたとき、各Xで次の等式：

    (derivedRestrictScalars f).map ((derivedComplexCompletionUnit S (f a)).app X)
      ≫ e.hom.app X
      = (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars f).obj X)

SのR平坦性、Noether性、有限生成性、a正則性、有界ねじれ、古典的完備性は要求しない。
当面のBS利用は上有界対象で十分であり、共通側がまず上有界版を提供する場合も使用できる。
利用工程：B4-6で、具体的基底射A→raw包（またはp正則な旧ねじれ商）について、
A加群としての実p導来完備化と、raw環自身上の実p導来完備化を標準単位を保って比較する。
この比較は、既存の環としてのPDCompletionH0候補へA上の導来比較・平坦性を接続するために必要。
既存APIで足りない点：DerivedRestrictionは実係数制限とホモロジーの自然比較、
CompletionQuotientは同じ係数環上での標準完備化単位の商比較を供給するが、
今回の共有HomologicalAlgebraとインターフェースの検索では両関手の上記交換APIを確認できなかった。
待つ工程：係数環の異なる二つの実完備化・環H0候補の標準単位付き接続のみ。
独立作業：今回の同じA上の実自由δ射・通常包・分冪表示環のTor、mod p、実完備化比較、
相対入力と具体的基底変更の比較は続行できる。一般の完備化交換補題はBS内で重複実装しない。
他チャットへのG8送信は未許可であり、送信していない。

### 今回の検証境界

今回5モジュール25公開宣言を対象ビルド・B4全体pure監査で検証した。
正則raw入力と具体的通常テンソルの比較18宣言、G7交換入力を保持した実自由δ射の比較7宣言を区別する。
既存のp局所性・p正則性・mod p正則性・ghost単射・指定単元δ(p)は中間仮定として保持する。
G4・G7・G8等の仮定・共通APIを解消したとは数えず、完全忠実平坦根付き拡大の引用なし存在と一般B4は未完成。

### 次工程の登録：raw除算包の残余商での次入力の正則性

BS専用DeltaAdjoinDivisionResidueRegular.leanで、任意の元族σに対する既存raw(p,d)残余商の
標準係数射・忠実平坦性を再利用し、A/(p,d,a_s)で正則な元の像がraw残余商でも正則となることを証明する。
源のp正則性から自由δ多項式環のp正則性はMathlibの平坦基底変更で供給する。
d=pではraw(p,p)残余商と実p商の標準同型を構成し、次入力のmod p正則性へ接続する。
この工程は次の除算段・複数生成元への拡張用であり、raw環自身のp正則性やCFFを一般族で結論しない。

### 次工程の登録：Frobenius入力の係数イデアルと次段正則性

BS専用DeltaPDivisionNextInput.leanで、任意元族y:σ→Aについて、
既存deltaDivisionFirstBaseIdeal (p:A) (φ∘y)と同じp乗入力のイデアルの一致を証明する。
次入力xのA/(p,y_s^p)での正則性から、raw A{φ(y_s)/p}の実p商での像の正則性へ接続する。
定数一元族ではこの係数イデアルを具体的な(p,y^p)主2生成イデアルに同定する。
δ(p)の単元性・ghost単射等は既存残余平坦性に必要な仮定として明示し、CFFを結論しない。

## B4-6：raw除算包の残余商での次入力の正則性（2026-10-15）

DeltaAdjoinDivisionResidueRegular.leanで、任意の元族σに対し、適切な係数商A/(p,d,a_s)で
正則な元の像がraw(p,d)残余商でも正則となることを証明した。
既存の標準残余係数射と忠実平坦性、Mathlibの正則性の平坦基底変更を再利用した。
自由δ多項式環のp正則性は元のAのp正則性から内部で供給する。
d=pの場合はraw(p,p)残余商と実p商を標準代表元を保つ同型で比較し、次入力のmod p正則性へ移した。
5公開宣言の対象3263ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
一般元族のraw環自身のp正則性・CFFは結論しない。

### 次工程の登録：二段のraw p除算包のp正則性

BS専用DeltaPDivisionTwoStep.leanで、一元raw A{φ(y₀)/p}から、その係数像j(y₁)の
raw p除算へ進む二段環を扱う。Aのp正則性、y₀のmod p正則性、y₁のA/(p,y₀^p)での
正則性、各自由δ環のghost単射、指定単元δ(p)を仮定し、二段環のp正則性を証明する。
次段で必要なδ(p)の単元性は標準δ射による指定単元の像から内部で供給する。
一般族のCFF、ghost単射の一般定理、完備化後の平坦性、一般B4は結論しない。

## B4-6：Frobenius入力の係数イデアルと次段正則性（2026-10-15）

DeltaPDivisionNextInput.leanで、任意元族yについて(p,φ(y_s))=(p,y_s^p)を証明した。
定数一元族の具体的イデアル(p,y^p)との一致も証明し、次入力の係数商での正則性を
raw A{φ(y_s)/p}の実mod p商へ移す公開定理を得た。
3公開宣言の対象3264ジョブ・B4全体pure監査成功。標準3公理のみ。新sorry・公理・引用なし。
ghost単射と指定単元δ(p)は明示した中間仮定であり、一般B4の完成とは数えない。

## B4-6：二段のraw p除算包のp正則性（2026-10-15）

DeltaPDivisionTwoStep.leanで、B₀=A{φ(y₀)/p}の具体的なδ構造E₀と標準射j₀に対して、
B₁=B₀{φ_E₀(j₀(y₁))/p}のp正則性を証明した。入力はAのp正則性、y₀のmod p正則性、
y₁のA/(p,y₀^p)での正則性、各段の自由δ環のghost単射、指定単元w=δ_A(p)である。
二段目のδ(p)の単元性はwの標準射による像から供給し、次入力の正則性は既存残余忠実平坦性から供給する。
3公開宣言の対象3766ジョブ成功。今回3モジュール計11宣言の直接pure依存監査成功、
標準3公理のみ。新sorry・公理・引用なし。既存André引用には依存しない。
B4全体監査の依存再ビルドは、共有KoszulOneCoordinates.lean:45の未解決ゴールにより失敗した。
共有ファイルは編集していない。今回の対象ビルド・直接監査成功と、全体監査未通過を区別する。
一段目の2モジュールは当初のB4全体監査にも成功していた。
一般CFF根付き拡大・一般B4全射性は未完成。次は二段除算と同時二入力除算の標準δ同型を構成し、
このp正則性を同時入力へ移す。ghost単射の一般補題等の待合せは継続する。

### 次工程の登録：同時族と二段raw除算の標準δ同型

BS専用DeltaAdjoinDivisionSum.leanで、任意の元族a:σ→A,b:τ→A、d:Aについて、
A{(a,b)/d}とA{a/d}{j(b)/j(d)}の具体的な標準環同型を構成する。
両方向のδ両立性、元の係数射と左右の除算変数の公式を証明する。
既存existsUnique_deltaAdjoinDivisionHomを再利用し、p正則性や平坦性を構成の前提にしない。
BS専用DeltaPDivisionPairRegular.leanで、この同型と二段p正則性を使い、
二つのFrobenius入力の同時raw p除算包のp正則性へ接続する。
既存のghost単射・指定単元・係数商での正則性の仮定を保持し、一般CFFは結論しない。

同じ工程でDeltaPDivisionFrobeniusShift.leanの従来privateなδ射外延性の重複を除き、
新モジュールの公開deltaAdjoinDivisionHom_extを再利用する。依存方向は
DeltaAdjoinDivision → DeltaAdjoinDivisionSum → DeltaPDivisionFrobeniusShiftとし、循環を作らない。
既存Frobenius平行移動の公開型・公式は維持する。

## B4-6：同時族と二段raw除算の標準δ同型（2026-10-15）

DeltaAdjoinDivisionSum.leanで、任意元族a:σ→A,b:τ→A,d:Aに対して、
A{(a,b)/d}≃A{a/d}{j(b)/j(d)}を構成した。元の係数射、左右の初期除算変数の公式と、
同型の両方向のδ両立性を証明した。p正則性、ghost単射、非零因子性、平坦性は仮定しない。
18公開宣言の対象2059ジョブ成功。既存FrobeniusShiftのprivate外延性を新公開定理へ統合し、
公開型を維持した。FrobeniusShift自体も再ビルド成功。
両モジュール計31公開宣言の直接pure監査成功、標準3公理のみ。新sorry・公理・引用なし。
B4全体監査は二入力正則性の検証後に再実行する。共有CochainConeCoordinatesの作業中エラーを
一度観測したが、共有ソースは編集せず、修正済みの現在ソースを使う対象再ビルドを開始した。
この同型は有限・一般族への逐次構成を比較するための成果であり、一般B4全射性やCFFは未完成。

### 次工程の登録：標数pの根関係のp乗商での後続正則性

BS専用DeltaRootPowerSubsetRegular.leanで、標数pの任意係数環Aと元族b:σ→A、
任意の先行部分集合Tについて、s∉TならX_s^p-b_sは先行根関係のp乗
((X_t^p-b_t)^p : t∈T)で割った多項式環でも正則であることを証明する。
標数pのp乗展開で先行イデアルを指数p²の既存根関係イデアルへ同定し、
既存の部分集合商表示と残り変数のモニック正則性を再利用する。
これは二段・有限段除算に必要な係数商上の正則性を具体的な独立根関係で供給する工程。
δ構造・ghost単射・導来完備性は不要であり、CFF・一般B4を結論しない。

## B4-6：二入力の同時raw p除算包のp正則性（2026-10-15）

DeltaPDivisionPairRegular.leanで、二つのFrobenius入力φ(y₀),φ(y₁)の同時raw p除算包の
p正則性を証明した。二段除算との標準δ同型と、既存二段p正則性を再利用した。
y₀のmod p正則性、y₁のA/(p,y₀^p)での正則性、各段の自由δ環のghost単射、
Aのp正則性と指定単元δ(p)を明示して保持する。平行移動同型からp乗入力版も得た。
2公開宣言の対象3768ジョブ成功。B4監査の全import依存4249ジョブ再ビルド成功後、
B4全体pure監査も成功。標準3公理のみ。共有側の一時的なビルドエラーは現在解消している。
新sorry・公理・引用なし。André引用に相対的な成果ではないが、中間仮定を解消したものではない。
一般CFF根付き拡大と一般B4全射性は未完成のまま保持する。

## B4-6：先行根関係のp乗商での後続正則性（2026-10-15）

DeltaRootPowerSubsetRegular.leanで、p=0となる任意係数環A、元族b:σ→A、任意部分集合Tについて、
先行根関係のp乗のイデアルが指数p²の既存根関係イデアルと一致することを証明した。
s∉TならX_s^p-b_sがこの商で正則となることを、既存部分集合商表示とモニック性から証明した。
正確な仮定は[CharP A p]ではなく(p:A)=0であり、零環も個別に処理して含める。
δ構造、p正則性、ghost単射、導来完備性、先行集合の有限性は仮定しない。
2公開宣言の対象3515ジョブ成功、警告なし。最終ソースに対するB4全体pure監査も成功、
標準3公理のみ。今回3新規モジュール計22公開宣言を全て専用監査で検査した。
新sorry・公理・引用なし。既存André引用にも依存しない。
次は係数環のmod p変更を通じて、この正則性を二入力除算の具体的多項式源の仮定へ供給する。
一般CFF根付き拡大・一般B4全射性は未完成。共通G3/G4/G6/G7/G8等の待合せと区別する。

### 次工程の登録：根関係のp乗部分集合商と係数商の標準比較

BS専用DeltaRootPowerSubsetBaseQuotient.leanで、任意係数イデアルI⊂A、先行部分集合Tと
根係数b:σ→Aについて、A[X]/(I·A[X]+((X_t^p-b_t)^p:t∈T))と
(A/I)[X]/((X_t^p-b̄_t)^p:t∈T)の標準同型と代表元公式を構成する。
既存の二重商・多項式係数商比較を再利用し、新しい一般完備性やTor補題は作らない。
I=(p)の場合、先行集合の外の根関係が実際の(p,先行関係p乗)商でも正則であることを証明する。
BS専用DeltaRootPairInputRegular.leanで、この正則性を二つの異なる根関係の
mod p正則性および(p,最初の関係p乗)商での正則性として供給する。
共通側のghost単射・完全平坦性・完備化比較の待合せは引き続き保持する。

### 次工程の登録：具体的根関係二入力のraw p正則性

BS専用DeltaRootPairRawRegular.leanで、p正則δ係数環Aのrank-one変数多項式δ環において、
異なる二つの根関係X_s^p-b_s,X_t^p-b_tのFrobenius像を同時にp除算する具体的raw環の
p正則性を証明する。多項式環のp正則性は既存の平坦基底変更から、二つの入力の
正則性はDeltaRootPairInputRegularから、δ(p)の単元は係数の指定単元の像から供給する。
二段の自由δ環のghost単射は引き続き明示仮定とする。G4受領や一般CFFの証明とは数えない。

## B4-6：先行根関係のp乗部分集合商と係数商の標準比較（2026-10-15）

DeltaRootPowerSubsetBaseQuotient.leanで、任意係数イデアルIと先行部分集合Tについて、
係数商変更と先行根関係p乗による商の標準同型を構成し、全多項式代表元上の公式を証明した。
この比較部分はpの素数性を要しない。I=(p)に適用し、残りの根関係の正則性を
実際のA[X]/(p,先行関係p乗)で証明した。この部分はp素数を仮定し、零環も含む。
4公開宣言の対象3516ジョブ成功、警告なし。B4全体pure依存監査成功、標準3公理のみ。
新sorry・公理・引用なし。一般完全忠実平坦性・一般B4全射性は未完成のまま保持する。

## B4-6：二つの独立根関係のraw除算への正則入力（2026-10-15）

DeltaRootPairInputRegular.leanで、任意係数環・任意根係数族に対し、各根関係の
多項式環mod pでの正則性と、異なる後続根関係の(p,先行根関係p乗)商での正則性を証明した。
先行部分集合を空集合・一元集合へ特殊化し、実際の商イデアルへ同定した。
p素数以外の係数環の正則性、δ構造、ghost単射、完備性、非零性は不要。
2公開宣言の対象ビルド成功（結合対象3772ジョブ中、本モジュールは成功、後続raw接続は修正中）。
B4全体pure依存監査成功、標準3公理のみ。新sorry・公理・引用なし。
この入力供給を、後続の具体的raw除算包のp正則性・一般CFFそのものと混同しない。

## B4-6：二つの独立根関係の具体的raw p除算包のp正則性（2026-10-15）

DeltaRootPairRawRegular.leanで、p正則δ係数環A、任意根係数族b:σ→Aと異なる添字s,tについて、
rank-one変数多項式δ環P=A[X_σ]の根関係X_s^p-b_s,X_t^p-b_tのFrobenius像を
同時にp除算した具体的raw環のp正則性を証明した。指定単元w=δ_A(p)と、
Pおよび第一段raw環上の一変数自由δ環のghost単射を明示仮定として保持する。
P自身のp正則性は既存平坦基底変更、入力のmod p・先行p乗商での正則性は前工程、
Pのδ(p)の単元はwの係数像から内部で供給する。係数環と根変数は別の任意宇宙に対応する。
対象3772ジョブ成功（共有LocalFlatnessCriterionの既存長行警告のみ）。最終B4全体pure監査成功。
今回3モジュール計7公開宣言を全てassert_no_sorry・公理依存出力で検査し、標準3公理のみ。
新sorry・公理・外部引用なし。既存André引用にも依存しない。
これは具体的二入力の証明済み成果であり、ghost単射の一般入力G4や一般CFF・一般B4全射性は未完成。
次は有限族へ拡張するため、raw除算包の再添字付け・一入力追加の標準比較と有限段の帰納を進める。

### 次工程の登録：raw除算の再添字付けと空族比較

BS専用DeltaAdjoinDivisionReindex.leanで、任意添字写像ρ:σ→τとa_s=b_(ρs)から、
同じ係数δ環・除数を持つraw包間の具体的δ射を構成する。添字同値の場合の
標準環同型、δ両立性、係数・変数公式を証明する。既存の指定解普遍性と公開外延性を再利用する。
BS専用DeltaAdjoinDivisionEmpty.leanで、空族raw包と元のδ係数環の標準同型を構成し、
有限入力帰納の零段を供給する。平坦性・完備性・p正則性は同型構成の仮定にしない。
BS専用DeltaPDivisionFamilyStep.leanで、任意先行族に一入力を追加した同時raw p除算包の
p正則性を、先行raw包のp正則性と適切な係数商での次入力の正則性から証明する。
各自由δ環のghost単射と指定単元δ(p)は明示仮定として保持し、一般CFFとは区別する。

### 次工程の登録：独立根関係の任意有限族raw包のp正則性

BS専用DeltaRootFiniteRawRegular.leanで、p正則δ係数環A、根係数族b:σ→A、任意有限集合T⊂σに対し、
rank-one多項式δ環A[X_σ]でTの根関係のFrobenius像を同時にp除算したraw環のp正則性を
有限集合の帰納で証明する。空族比較・再添字付け・任意先行族への一入力追加を使用する。
各有限先行族の源の自由δ環と各先行raw包上の一変数自由δ環のghost単射、および指定単元δ(p)を保持する。
根関係の正則性と多項式環のp正則性は内部供給し、一般CFF・G4解消とは数えない。

## B4-6：raw除算の再添字付け（2026-10-15）

DeltaAdjoinDivisionReindex.leanで、任意添字写像と対応する入力の一致から標準δ射を構成した。
添字同値については標準環同型、両方向のδ両立性、係数射・除算変数の公式を証明した。
既存普遍性・公開外延性を再利用し、p正則性・ghost単射・平坦性を仮定しない。
9公開宣言の対象2060ジョブ成功、警告なし。B4全体pure依存監査成功、標準3公理のみ。
新sorry・公理・引用なし。有限入力の一添字追加による帰納で使用する。

## B4-6：空族raw除算包の標準δ同型（2026-10-15）

DeltaAdjoinDivisionEmpty.leanで、空族のraw除算包と元の係数環の標準環同型を構成し、
両方向のδ両立性と係数射上の公式を証明した。既存の指定解普遍性・外延性を再利用した。
7公開宣言の対象2060ジョブ成功、警告なし。B4全体pure依存監査成功、標準3公理のみ。
新sorry・公理・引用なし。有限族のp正則性帰納の零段として使用する。

## B4-6：任意先行族への一入力追加のp正則性（2026-10-15）

DeltaPDivisionFamilyStep.leanで、任意先行族yのraw A{φ(y_s)/p}から一入力xの除算へ進む
実二段環と、先行族とxの同時raw除算包のp正則性を証明した。
先行raw環のp正則性とxのA/(p,y_s^p)での正則性を明示仮定にし、
次段に必要なmod p正則性は既存残余忠実平坦性、δ(p)の単元は元の指定単元の像で供給した。
各自由δ環のghost単射・元のAのp正則性・指定単元δ(p)を保持する。
係数環と先行添字は独立の任意宇宙に対応する。
2公開宣言の対象3767ジョブ成功（共有側の既存長行警告のみ）。B4全体pure監査成功、標準3公理のみ。
新sorry・公理・引用なし。有限族の帰納段として使用し、一般CFF・B4全射性完成とは区別する。

## B4-6：任意有限集合の独立根関係のraw p除算包のp正則性（2026-10-15）

DeltaRootFiniteRawRegular.leanで、p正則δ係数環Aと任意根係数族b:σ→Aに対し、
任意有限集合Tの独立根関係X_t^p-b_tのFrobenius像を同時p除算した具体的raw環の
p正則性を有限集合の帰納で証明した。空族比較、再添字付け、一入力追加、
任意先行根関係のp乗商での後続正則性を再利用した。
指定単元w=δ_A(p)、各有限族の多項式源上自由δ環のghost単射、各先行raw包のp正則性から
その包上の一変数自由δ環のghost単射を供給する入力を明示して保持する。
後者は帰納仮定のp正則性を引数に取る形であり、G4を後から供給するときに
全有限raw包のp正則性を先に仮定する循環を避ける。G4自体の証明・受領とは数えない。
係数環・根変数は任意の別宇宙に対応する。入力根関係の正則性や源の多項式p正則性は内部供給する。
2公開宣言の対象3772ジョブ成功（共有側の既存長行警告のみ）。最終B4全体pure監査成功。
今回4モジュール計20公開宣言を全て専用監査で検査し、標準3公理のみ。新sorry・公理・引用なし。
一般CFF根付き拡大・一般B4全射性は未完成。次は有限raw包のmod p係数射の忠実平坦性と、
任意族へ移す有限部分族の有向比較を進める。共通基盤の待合せを一般論開始の条件にはしない。

### 次工程の登録：Frobenius根関係のmod p係数商のp²乗根表示

BS専用DeltaRootFrobeniusCoefficient.leanで、rank-one多項式δ環P=A[X_σ]の
Q=P/(p,φ(X_s^p-b_s))を既存MonicPowerFamilyCover (p²) σ (A/p) (b̄_s^p)へ
標準同型で比較する。既存の係数商比較・標数pのp乗展開・通常根添加表示を再利用する。
係数商の標準射A/p→Qの具体式と、その射に関する忠実平坦性を証明する。
この係数商表示にはAのp正則性や完備性・有限性・ghost単射は仮定しない。
BS専用DeltaRootRawModPFlat.leanで、既存raw残余係数射の忠実平坦性と合成し、
raw P{φ(X_s^p-b_s)/p}/pの標準係数射A/pに関する忠実平坦性を証明する。
Aのp正則性・指定単元δ(p)・必要なghost単射は明示し、raw自身のp正則性や完備化後CFFとは区別する。

## B4-6：Frobenius根関係の初期係数商のp²乗根表示（2026-10-15）

DeltaRootFrobeniusCoefficient.leanで、rank-one多項式δ環P=A[X_σ]について、
Q=P/(p,φ(X_s^p-b_s))を既存のA/p上のp²乗根添加環へ標準同型で比較した。
任意多項式代表元・元の係数上の公式を証明し、実標準係数像を持つA/p→Qを公開した。
その係数射に関してQが忠実平坦であることを既存通常根添加の忠実平坦性から証明した。
添字集合の有限性、Aのp正則性、ghost単射、完備性は仮定しない。零環も含む。
12公開宣言の対象3519ジョブ成功、警告なし。属性付き代数定義も含め全宣言を専用監査へ登録した。
B4全体pure依存監査成功、標準3公理のみ。新sorry・公理・引用なし。
これは初期係数商の忠実平坦性であり、raw本体や導来完備化後の一般CFF・B4全射性完成とは区別する。

## B4-6：根関係raw同時p除算包の実mod p商の忠実平坦性（2026-10-15）

DeltaRootRawModPFlat.leanで、p正則δ係数環Aと任意根係数族b:σ→Aについて、
rank-one多項式δ環P=A[X_σ]のraw P{φ(X_s^p-b_s)/p}の実p商への標準射A/pを構成し、
元の係数の標準商像を与える公式と、その射に関する忠実平坦性を証明した。
初期係数商の忠実平坦性と既存raw残余商の忠実平坦性をスカラー塔で合成し、
raw(p,p)残余から実p商へ係数を保つ代数同型で移した。
Aのp正則性、指定単元w=δ_A(p)、P上の自由δ環のghost単射を明示仮定として保持する。
多項式環およびその自由δ環のp正則性、δ_P(p)の単元性は内部供給する。
添字集合の有限性は不要。raw環そのもののp正則性はこの定理の仮定・結論に含めない。
9公開宣言の対象3520ジョブ成功、警告なし。最終B4全体pure依存監査成功、標準3公理のみ。
今回2モジュール計21公開宣言を、属性付き代数定義も含め専用監査で全て検査した。
新sorry・公理・外部引用なし。既存André引用にも依存しない。
これは補助φ/p除算包のmod p忠実平坦性であり、一般d除算・完全化・実導来完備化を通じた
既存perfectoid候補の標準射のCFFや一般B4全射性を完成したとは数えない。
次は実mod p比較と元の係数射のスカラー制限を接続し、有限族のp正則性と併せて
共通の完全平坦性判定へ渡す具体的入力を整える。任意族への有限部分族比較も継続する。

### 次工程の登録：元の係数射とraw実mod p基底変更

BS専用DeltaRootRawCoefficientBaseChange.leanで、A→P→raw包の実係数射とA代数構造を公開し、
(A/p)⊗_A raw包≃raw包/pを、前工程の標準A/p係数射に関する代数同型として構成する。
既存Mathlibの商テンソル比較と既存標準係数公式を再利用し、新しい一般商テンソル定義は作らない。
この同型から、既存IsCompletelyFaithfullyFlatの忠実平坦性側に現れる実基底変更加群の忠実平坦性を証明する。
BS専用DeltaRootRawRelativeModPKoszul.leanで、raw包のp正則性を明示入力として、
元のA上の実p Koszul列と実導来還元の比較を既存共通Koszul比較から構成する。
共通G3の一般完全平坦性判定は重複実装せず、G3を受領したとは数えない。

### 次工程の登録：raw包の元のA→A/pに沿う高次Tor消滅と実導来比較

BS専用DeltaRootRawRelativeDerivedModP.leanで、前工程のA上Koszul比較を用いて、
Aとraw包のp正則性から、実A→A/p係数拡大の全高次Tor消滅を証明する。
標準通常基底変更同型と組み合わせ、実導来還元を実raw包/pの次数零対象へ同定する。
既存の導来基底変更・係数制限のホモロジー比較を再利用し、G3一般判定を新設しない。

## B4-6：元の係数射に沿うraw包の通常mod p基底変更（2026-10-15）

DeltaRootRawCoefficientBaseChange.leanで、元のA→P→raw包の実係数射を公開し、
既存のA代数構造の係数射と一致することを証明した。既存のA加群作用を維持している。
Aのp主イデアルの拡張がraw包自身のp主イデアルとなることから、
(A/p)⊗_A raw包と実raw包/pの標準A/p代数同型を構成し、1⊗zの実標準商像の公式を証明した。
既存実mod p商の忠実平坦性を移し、IsCompletelyFaithfullyFlatの通常基底変更側に現れる
具体的な加群の忠実平坦性を得た。完全平坦性側はこの工程では結論しない。
8公開宣言の対象ビルド成功（結合対象3690ジョブ中、本モジュール成功）。B4全体pure監査成功。
標準3公理のみ。新sorry・公理・引用なし。元のp正則性・指定単元δ(p)・ghost単射は保持する。

## B4-6：元のA上の根関係raw包の実p Koszul比較（2026-10-15）

DeltaRootRawRelativeModPKoszul.leanで、元のA加群としてraw包の実p列を構成した。
raw包のp正則性を明示入力とし、短完全性と実p商へのKoszul添加写像の擬同型性を証明した。
さらにAのp正則性を用い、実A→A/p導来還元をAへ係数制限した対象が、
実raw包/pの次数零対象となる標準同型を既存共通Koszul比較から構成した。
7公開宣言の対象3690ジョブ成功、警告なし。B4全体pure依存監査成功、標準3公理のみ。
新sorry・公理・引用なし。一般完全平坦性やG3解消とは区別し、raw包自身のp正則性入力も保持する。

## B4-6：元の係数環上のraw包の高次Tor消滅と実導来還元比較（2026-10-15）

DeltaRootRawRelativeDerivedModP.leanで、Aと具体的根関係raw包のp正則性を明示入力として、
元のA→A/pに沿う実係数拡大の全高次Tor消滅を証明した。既存共通の導来基底変更と
係数制限のホモロジー比較、前工程の実Koszul同型を再利用した。
通常の実係数拡大加群を標準A/p作用付きの実raw包/pへ同定し、
実導来還元がその次数零対象となる公開同型を構成した。
Tor消滅自体はAおよびraw包のp正則性を仮定し、ghost単射・指定単元は通常比較側の入力として保持する。
3公開宣言の対象3692ジョブ成功、警告なし。最終B4全体pure依存監査成功、標準3公理のみ。
今回3モジュール計18公開宣言を属性付き代数定義も含め全て専用監査で検査した。
新sorry・公理・外部引用なし。André引用にも依存しない。
これは元のA→A/pに関するTor・導来比較であり、G3の任意(p)消滅加群への完全平坦性判定や
完備化・完全化後の一般CFF、一般B4全射性の完成とは数えない。
次は元のA上の実導来完備化単位とmod p比較を接続し、有限族のp正則性との具体的再添字比較で
raw包のp正則性入力を内部供給する。共通G3・G6・G7・G8の一般API待合せとは分けて進める。

### 次工程の登録：根関係raw包の実導来完備化単位とmod p比較

BS専用DeltaRootRawRelativeCompletionModP.leanで、元のA上の実p導来完備化単位をA→A/pで還元した射が
同型となることを既存共通CompletionQuotientから証明する。Aとraw包のp正則性を明示した
実導来還元比較を合成し、A上の実導来完備化のmod p比較と標準単位の可換性を証明する。
raw環上の導来完備化との係数制限交換G8や、古典的完備化との同一視は結論しない。
BS専用DeltaRootFiniteFamilyRegular.leanで、有限添字σの全族raw包を、Finset.univに関する
前工程の有限部分集合raw包と標準再添字同型で比較し、全族raw包自身のp正則性を内部供給する。
ghost入力は有限部分集合版と同じく明示し、G4解消と混同しない。

### 次工程の登録：有限根関係族のTor・実導来完備化比較のp正則性入力の内部供給

BS専用DeltaRootFiniteRelativeModP.leanで、有限添字全族のraw包のp正則性を内部で供給し、
元のA→A/pに沿う高次Tor消滅、実導来還元、A上の実導来完備化のmod p同型、標準単位の可換性を公開する。
係数環のp正則性、指定単元δ(p)、有限段ghost入力、標準mod p比較に必要な全族源のghost入力は明示する。
raw包のp正則性そのものは追加仮定しない。有限性を一般B4の仮定に追加したとは解釈せず、
任意族への移送に先立つ実有限段の成果として管理する。G3/G4/G8の一般API解消とは区別する。

## B4-6：根関係raw包のA上の実導来完備化とmod p比較（2026-10-15）

DeltaRootRawRelativeCompletionModP.leanで、Aのp正則性から、元のA上の標準p導来完備化単位を
実A→A/p還元した射が同型となることを、既存共通CompletionQuotientから証明した。
Aとraw包のp正則性を明示した実導来還元比較を合成し、元のA上の実導来完備化の
mod p同型と標準単位との可換性を証明した。ghost単射・指定単元δ(p)は同型側で保持する。
3公開宣言の対象3703ジョブ成功、警告なし。B4全体pure依存監査成功、標準3公理のみ。
新sorry・公理・引用なし。raw環上の完備化との係数制限比較G8、古典的完備化との比較、
一般CFF・一般B4全射性完成とは区別する。

## B4-6：有限添字全族raw包のp正則性（2026-10-15）

DeltaRootFiniteFamilyRegular.leanで、有限添字σの全族raw P{φ(X_s^p-b_s)/p}について、
Finset.univを添字とする既存有限部分集合raw包との標準再添字同型からp正則性を証明した。
Aのp正則性、指定単元δ(p)、有限部分集合の自由δ源のghost単射、先行raw包のp正則性から
一変数自由δ環のghost単射を供給する入力を保持する。raw包のp正則性自体は追加仮定しない。
係数環・根変数は独立の任意宇宙に対応する。1公開宣言の対象3773ジョブ成功。
共有側の既存長行警告のみ。B4全体pure依存監査成功、標準3公理のみ。新sorry・公理・引用なし。
この有限性は有限段の証明の仮定であり、一般B4目標へ追加した制約ではない。

## B4-6：有限根関係全族のTor・実導来還元・実導来完備化比較（2026-10-15）

DeltaRootFiniteRelativeModP.leanで、有限添字全族のraw包自身のp正則性を内部供給し、
元のA→A/pに沿う全高次Tor消滅、実導来還元の実raw包/pへの同型、元のA上の
実導来完備化のmod p同型と標準単位の可換性を証明した。
raw包のp正則性自体は追加仮定しない。Aのp正則性、指定単元δ(p)、有限段の二種類のghost入力を保持し、
通常mod p比較を使う同型側では全族源のghost単射も明示する。
4公開宣言の対象3791ジョブ成功（共有側の既存長行警告のみ）。最終B4全体pure依存監査成功。
今回3モジュール計8公開宣言を全て専用監査で検査し、標準3公理のみ。新sorry・公理・外部引用なし。
André引用にも依存しない。有限性を一般B4目標へ追加せず、具体的有限段の成果として管理する。
raw環上の完備化との係数制限交換G8、任意族への移送、一般CFF・一般B4全射性は未完成。
次は有限raw包の再添字射の合成・有限部分族の有向比較を整え、任意族のp正則性と
実導来比較へ移す。G3等を使う工程のみを別の待合せとして保持する。

### 次工程の登録：raw再添字射の関手性と有限部分族有向系

BS専用DeltaAdjoinDivisionReindexFunctorial.leanで既存再添字射の恒等・合成公式を証明する。
BS専用DeltaAdjoinDivisionFiniteSystem.leanで、任意元族a:σ→Aの有限部分族raw包、
有限集合包含に沿う標準δ遷移射、係数・変数公式、DirectedSystem条件、全族raw包への両立射を構成する。
BS専用DeltaAdjoinDivisionFiniteColimit.leanで、Mathlibの環の有向余極限を使い、
そのW₂切断と標準δ構造を各段から移す。有限部分族余極限と全族raw包の標準δ同型に接続する。
p正則性・有限性・ghost単射はこの構成の仮定にせず、新しい共通余極限一般論を重複構築しない。
これらを任意族のp正則性移送に使用する。一般CFF・B4全射性完成とは区別する。

## B4-6：raw再添字射の恒等・合成公式（2026-10-15）

DeltaAdjoinDivisionReindexFunctorial.leanで、既存のraw再添字射の恒等・合成公式を証明した。
指定解の普遍性と公開外延性を再利用し、p正則性・ghost単射等を仮定しない。
2公開宣言の対象2061ジョブ成功、警告なし。B4全体pure依存監査成功、標準3公理のみ。
新sorry・公理・引用なし。有限部分族の有向系と全族比較に使用する。

### 次工程の登録：有限部分族raw環余極限と全族raw包の標準δ同型

BS専用DeltaAdjoinDivisionFiniteColimitEquiv.leanで、余極限の単元部分族変数が全ての関係を満たすことを示し、
既存raw普遍性から全族raw包→有限部分族余極限を構成する。
既存の逆方向射との二つの合成を外延性・環余極限普遍性から証明し、標準δ同型を得る。
BS専用DeltaAdjoinDivisionFamilyRegular.leanで、有限部分族のp正則性から全族raw包のp正則性を移す。
Mathlib環余極限の零の有限段判定を用い、一般環余極限定義や一般共有補題を再実装しない。
独立根関係の前工程の有限部分集合p正則性を適用し、任意添字族のraw根関係p除算包へ接続する。
有限段ghost入力は保持し、一般G4・CFF・B4全射性完成とは区別する。

## B4-6：有限部分族raw包の有向系（2026-10-15）

DeltaAdjoinDivisionFiniteSystem.leanで、任意元族の各有限部分族raw包、有限集合包含の標準δ射、
係数・初期変数の公式、恒等・合成条件とMathlib DirectedSystem、全族raw包への両立標準δ射を構成した。
p正則性・ghost単射・平坦性を仮定しない。9公開宣言（DirectedSystemインスタンスを含む）の
対象2065ジョブ成功、警告なし。B4全体pure監査成功、標準3公理のみ。新sorry・公理・引用なし。
有限部分族の余極限と全族の具体的比較に使用する。一般B4全射性完成とは区別する。

### 次工程の登録：任意根関係族のraw p正則性

BS専用DeltaRootFamilyRawRegular.leanで、有限部分集合の独立根関係の既存p正則性を、
任意族raw包の有限部分族余極限表示へ適用する。任意添字σについて、
raw A[X_σ]{φ(X_s^p-b_s)/p}自身のp正則性を証明する。
Aのp正則性・指定単元δ(p)・有限段の二種類のghost入力は明示して保持し、σの有限性を仮定しない。
G4一般入力やCFF・一般B4全射性の解消とは区別する。

## B4-6：有限部分族raw環余極限の標準δ構造（2026-10-15）

DeltaAdjoinDivisionFiniteColimit.leanで、Mathlib環余極限へ各有限部分族のW₂切断を移し、
標準δ構造、各有限段の標準δ射、全族raw包への両立標準δ射、元の係数δ射を構成した。
係数射は任意有限段を通ること、全族への射との合成が元の標準係数射であることも証明した。
p正則性・ghost単射・平坦性は不要。14公開宣言の対象2069ジョブ成功、警告なし。
B4全体pure依存監査成功、標準3公理のみ。新sorry・公理・引用なし。
全族raw包との逆方向射・標準同型は別工程であり、一般B4全射性完成とは区別する。

## B4-6：有限部分族raw環余極限と全族raw包の標準δ同型（2026-10-15）

DeltaAdjoinDivisionFiniteColimitEquiv.leanで、単元部分族の変数から余極限の標準除算変数を構成し、
任意有限段での変数公式と元の除算関係を証明した。既存raw包の普遍性から逆方向標準δ射を構成し、
δ射外延性・Mathlib環余極限普遍性によって両方向合成が恒等射となることを証明した。
任意族raw包と有限部分族raw環余極限の標準環同型、両方向のδ両立性、各有限段上の公式を得た。
p正則性・有限性・ghost単射・平坦性は仮定しない。12公開宣言の対象2070ジョブ成功、警告なし。
B4全体pure監査成功、標準3公理のみ。新sorry・公理・引用なし。一般B4完成とは区別する。

## B4-6：有限部分族から任意族raw包へのp正則性移送（2026-10-15）

DeltaAdjoinDivisionFamilyRegular.leanで、全有限部分族raw包のp正則性から、
その環余極限および全族raw包自身のp正則性を証明した。Mathlib環余極限の零の有限段判定を使い、
p倍の零関係を十分大きい有限段へ移して正則性を適用した。遷移射の単射性は不要。
全族との標準δ同型を再利用し、一般共有余極限補題を重複定義していない。
2公開宣言の対象ビルド成功（結合対象3779ジョブ）。B4全体pure監査成功、標準3公理のみ。
新sorry・公理・引用なし。具体的根関係族への適用は別工程であり、一般CFF・B4完成とは区別する。

## B4-6：任意根関係族のraw p除算包のp正則性（2026-10-15）

DeltaRootFamilyRawRegular.leanで、任意添字σと根係数族b:σ→Aについて、
rank-one多項式δ環P=A[X_σ]の全族raw P{φ(X_s^p-b_s)/p}自身のp正則性を証明した。
前工程の独立根関係の有限部分集合版と、任意族raw包の有限部分族余極限δ同型・正則性移送を適用した。
Aのp正則性、指定単元δ(p)、各有限部分族の自由δ源のghost単射、先行raw包のp正則性から
その包上の一変数自由δ環のghost単射を供給する入力を保持する。σの有限性は仮定しない。
係数環・根変数は独立の任意宇宙に対応する。1公開宣言の対象3779ジョブ成功。
共有側の既存長行警告のみ。最終B4全体pure依存監査成功、標準3公理のみ。
今回6モジュール計40公開宣言（DirectedSystemインスタンスを含む）を全て専用監査で検査した。
新sorry・公理・外部引用なし。André引用にも依存しない。
この成果で補助φ/p raw除算のp正則性に関する有限性の制約は外れた。
G4一般入力の解消、一般d除算・完全化・導来完備化後のCFF、一般B4全射性は未完成のまま保持する。
次は任意族のこのp正則性を既存の元のA上のTor・実導来完備化比較へ供給し、
共通の完全平坦性判定へ渡す具体的な任意族入力を整える。

### 次工程の登録：任意根関係族のTor・実導来完備化比較

BS専用DeltaRootFamilyRelativeModP.leanで、任意族のraw包のp正則性を内部供給し、
元のA→A/pに沿う高次Tor消滅、実導来還元、A上の実導来完備化のmod p同型と標準単位可換性を公開する。
有限段ghost入力および全族源ghost単射は明示し、raw包のp正則性・σの有限性は追加仮定しない。
BS専用DeltaRootFamilyCompletedModPFlat.leanで、この実完備化の実p還元のH0をraw包/pと
標準A/p線形同型で比較し、非零次数ホモロジー消滅と実H0のA/p忠実平坦性を証明する。
既存ホモロジー比較・実raw p商の忠実平坦性を再利用し、一般G3判定やG8係数制限交換は新設しない。

## B4-6：任意根関係族のTor・実導来還元・実導来完備化比較（2026-10-15）

DeltaRootFamilyRelativeModP.leanで、任意添字族のraw包のp正則性を内部供給し、元のA→A/pに沿う
高次Tor消滅、実導来還元の実raw包/pへの同型、元のA上の実導来完備化のmod p同型と標準単位可換性を証明した。
σの有限性、raw包自身のp正則性は追加仮定しない。Aのp正則性・指定単元δ(p)・有限段の二種類のghost入力を保持し、
通常比較を使う同型側では全族源のghost単射も明示する。
4公開宣言の対象3797ジョブ成功（共有側の既存長行警告のみ）。B4全体pure監査成功、標準3公理のみ。
新sorry・公理・引用なし。André引用にも依存しない。
共有DerivedBaseChangeRightTensorの商比較は両因子のTor消滅を保持しており、
G3の任意(p)消滅試験加群への判定をそのまま解消するAPIではないことを現行ソースで再確認した。
G3一般判定、G4一般ghost入力、G8完備化と係数制限交換、一般CFF・B4全射性は未完成のまま保持する。

## B4-6：任意根関係raw包の実導来完備化のmod pホモロジーと忠実平坦性（2026-10-15）

DeltaRootFamilyCompletedModPFlat.leanで、元のA上の実導来完備化をA→A/pで実還元した対象の
H0と、標準A/p作用付き実raw包/pとの線形同型を構成した。全ての非零次数の実ホモロジー消滅と、
その実H0のA/p忠実平坦性を証明した。既存の実導来比較・次数零ホモロジー比較・実raw p商の忠実平坦性を再利用した。
σの有限性やraw包のp正則性自体は追加仮定しない。係数環のp正則性、指定単元δ(p)、
有限段二種類と全族源のghost入力は保持する。対象はH0(Lmod p Complete_A,p Single(raw))であり、
H0(Complete_A,p Single(raw))/pとの比較や古典的完備化への置換を結論しない。
3公開宣言の対象3798ジョブ成功（共有側の既存長行警告のみ）。最終B4全体pure依存監査成功、標準3公理のみ。
今回2モジュール計7公開宣言を全て専用監査で検査した。新sorry・公理・外部引用なし。André引用にも依存しない。
一般G3判定、G4一般ghost入力、G8完備化と係数制限交換、一般d除算・完全化後のCFF、
一般B4全射性は未完成のまま保持する。これらを今回の実mod pホモロジー計算の完了と混同しない。
次は補助φ/p除算包のこの実導来計算を、自由δ射間の通常・導来pushout比較と一般d根添加候補へ
つなぐ既存APIの適用条件を再点検し、独立なBS比較を進める。

### 次工程の登録：一般d・任意元族の自由δ射の通常pushout比較

BS専用DeltaDivisionSourceAlgebras.leanで、任意元族c:σ→Aの実評価βと任意除数dの実射αに
対応する既存自由δ環の代数構造を公開する。既存の一元評価代数構造
DeltaDivisionSourceFiniteColimit.leanのdeltaDivisionSourceEvalAlgebraと、
DeltaPDivisionSourceTensor.leanのdeltaPDivisionSourceTargetAlgebraは、新一般定義の特殊化へ変更し公開型を維持する。
BS専用DeltaDivisionSourceTensor.leanで、任意d,cの実通常テンソルA_β⊗_{A{X}}A{Z}_αと
raw A{c_s/d}の両因子像を保つ標準環同型・係数A代数同型を構成する。
既存DeltaPDivisionSourceTensor.leanの公開定義・補題は、新一般比較を呼ぶ特殊化へ整理し、重複証明を避ける。
BS専用DeltaDivisionSourceTensorDelta.leanで、この通常テンソルのδ構造と両因子包含のδ両立性を
一般d,cについて証明する。既存DeltaPDivisionSourceTensorDelta.leanも特殊化へ整理し公開APIを維持する。
既存DeltaDivisionEvaluationSourceのraw普遍性を再利用する。Tor消滅・導来pushout離散性・完備化後CFFは
この通常pushout比較から結論せず、G7等を使う工程と分ける。共通ファイル・CLMST側は編集しない。

## B4-6：一般除数・任意元族の自由δ射の実代数構造（2026-10-15）

DeltaDivisionSourceAlgebras.leanで、任意元族への実評価βと任意除数の自由δ射α:x_s↦d z_sに沿う
実代数構造と係数射公式を公開した。既存の一元評価代数とp除算終域代数はその特殊化へ整理し、公開型を維持した。
4公開宣言および既存特殊化の対象3772ジョブ成功（共有側の既存長行警告のみ）。
B4全体pure依存監査成功、標準3公理のみ。新sorry・公理・引用なし。
任意d・任意元族の通常pushout比較へ使用する。導来pushout離散性・一般CFF・B4完成とは区別する。

## B4-6：一般d・任意元族の自由δ射の通常pushout表示（2026-10-15）

DeltaDivisionSourceTensor.leanで、任意dと任意元族cについて、実自由δ射α:x_s↦d z_sと評価β:x_s↦c_sに
沿う通常テンソルA_β⊗_{A{X}}A{Z}_αとraw A{c_s/d}の標準環同型を構成した。
両因子の標準像・純テンソル像・逆方向商元公式を証明し、元の係数A作用を保つ代数同型へ昇格した。
p正則性、ghost単射、有限性、dの非零因子性、完備性は仮定しない。
既存DeltaPDivisionSourceTensorの公開型を維持したまま一般比較の特殊化へ整理し、重複証明を除いた。
13新公開宣言と既存特殊化の対象3774ジョブ成功（共有側の既存長行警告のみ）。
B4全体pure監査成功、標準3公理のみ。新sorry・公理・引用なし。
これは通常pushout表示であり、導来pushout離散性・CFF・B4全射性完成とは区別する。

## B4-6：一般d通常pushoutのδ構造・δ普遍性（2026-10-15）

DeltaDivisionSourceTensorDelta.leanで、任意d,cの通常テンソルをraw包と比較してδ構造を構成し、
比較の両方向・両因子の標準包含のδ両立性と、その包含をδ射にするδ構造の一意性を証明した。
さらに、可換な二環射の自由δ因子側がδ射なら、通常pushoutからの延長も一意なδ射となる普遍性を証明した。
係数側のδ両立性は自由δ係数射と可換性から従うので追加仮定していない。
既存DeltaPDivisionSourceTensorDeltaの公開型を維持したまま一般比較の特殊化へ整理した。
p正則性・ghost単射・有限性・dの非零因子性・完備性は不要。7新公開宣言と既存特殊化を含む
B4監査の全import依存4276ジョブ再ビルド成功。一般版・旧特殊化・既存完備化利用先も成功した。
最終B4全体pure監査成功、標準3公理のみ。今回3モジュール計24新公開宣言を全て専用監査で検査した。
新sorry・公理・外部引用なし。André引用にも依存しない。
これは通常可換環pushoutの具体的δ普遍性であり、導来pushout離散性やG7、完備化後CFF、
一般B4全射性の完成とは区別する。共有・CLMSTファイルやルートimportは編集していない。
次は一般dのδ関係と既存自由δ射側の有限段Tor・Koszul証明を、BS原典・正本計画と照合し、
補助φ/p計算を一般d根添加候補へ結ぶ実比較を進める。

### 次工程の登録：一般d・任意有限δ座標の実Tor比較

BS担当の新規DeltaDivisionSourceFiniteTor.leanで、任意元族c:σ→A、除数d:A、
異なる有限座標s:Fin m→σ×ℕの源グラフ商について、自由δ射α:x↦d zに沿う実Torを
終域の実評価関係Koszulホモロジーで計算する。源側のKoszul分解は既存の証明を再利用する。
終域のKoszul分解が得られる場合の正次数Tor消滅も公開するが、その仮定を無条件に供給したとはしない。
既存DeltaPDivisionSourceFiniteTor.leanの一元φ/p比較は一般比較の特殊化へ整理し公開型を維持する。
有限商から全評価環への移行、G7、一般d終域の正則性、導来pushout離散性は別工程として保持する。
共通ファイル・CLMST・共有監査は編集せず、BS専用監査へ全新公開宣言を追加する。

## B4-6：一般d・任意有限δ座標の実Tor比較（2026-10-15）

DeltaDivisionSourceFiniteTor.leanで、任意d,cと異なる有限座標族sについて、
実自由δ射αに沿う実源グラフ商のTorを終域の実評価関係Koszulホモロジーと同型にした。
源の有限グラフ関係のKoszul分解は既存証明を再利用した。p正則性・ghost単射・完備性・
σの有限性は比較に不要で、空の有限座標族も含む。終域がKoszul分解を与える場合の正次数Tor消滅も証明した。
3新公開宣言の対象3519ジョブ成功、B4全体pure監査1809報告成功、標準3公理のみ。
新sorry・公理・外部引用なし。終域のKoszul分解という仮定を無条件に解消したとはしない。
有限源商と全評価環を区別し、G7・一般dの導来pushout離散性・CFF・一般B4全射性は未完成として保持する。

## B4-6：一元φ/pの有限源Torを一般比較へ接続（2026-10-15）

既存DeltaPDivisionSourceFiniteTorの比較同型と正次数Tor消滅を、
一般DeltaDivisionSourceFiniteTorのs(i)=(default,i)・d=p・c=φ(y)への特殊化に整理した。
旧公開型・正則性入力・後続のG7相対的導来比較は維持した。重複する比較・消滅の証明を除いた。
一元版と後続導来比較3862ジョブ、B4監査全import依存4277ジョブ成功。
警告は既存のLocalFlatnessCriterion長行、DerivedTensorPentagon設定コメント、
DeltaPDivisionSequentialKoszulUnitのhaveI形式のみ。最終B4全体pure監査1809報告成功、標準3公理のみ。
新sorry・公理・引用なし。今回の証明済み成果は有限源商の比較であり、
全評価環へのTor移送のG7、一般d根添加終域のKoszul分解、完全化後CFFは引き続き別工程。
著者版Lemma 2.43・Corollary 2.44・Theorem 7.14を確認し、補助φ/p計算のみから
一般d根添加候補の完全忠実平坦性を結論しない。一般B4は未完成として保持する。

### 次工程の登録：一般d根添加の深さ0における実Koszul分解

BS専用DeltaRootFirstEvaluationKoszul.leanを新設する。係数A、任意d:A、元族b:σ→A、
根用多項式環P=A[X_s]、その自由δ環L=P{Z_s}について、
g_s=C(C d) Z_(s,0)-C(X_s^p-C b_s)が異なる有限s上でKoszul分解を与えることを証明する。
変数交換でモニック根関係に移し、既存の有限根関係正則性を再利用する。
その後、既存DeltaDivisionSourceFiniteTorを用い、源の深さ0有限グラフ商について実Tor消滅を証明する。
dの正則性・p正則性・ghost単射・有限σ・完備性は追加しない。
正のδ深さの関係、全評価環への移行、完全化後CFFはこの有限深さ0計算から結論しない。
共通ファイル・CLMSTは編集しない。

## B4-6：一般d根添加の深さ0の実Koszul分解（2026-10-15）

DeltaRootFirstEvaluationKoszul.leanで、根用多項式δ環の自由δ環上の実評価関係について、
深さ0で変数を交換した像がモニック根関係の負になる公式を証明した。
既存の有限根関係の弱正則性を移し、任意d・任意の異なる有限根添字に対する
実評価Koszul分解と、実自由δ射に沿う深さ0有限源グラフ商の全正次数Tor消滅を証明した。
dの正則性・p正則性・ghost単射・有限σ・完備性は不要。零環と空の有限添字も含む。
4新公開宣言の対象3523ジョブ成功、B4全体pure監査1813報告成功、標準3公理のみ。
新sorry・公理・外部引用なし。一般dの有限源商に実際のTor消滅を供給した最初の段階である。
正のδ深さの正則性、全評価環のTor、完全化後CFF、一般B4全射性は未完成として区別する。

### 次工程の登録：一般d根添加の深さ0通常商の標準表示と忠実平坦性

BS専用DeltaRootFirstEvaluationQuotient.leanを新設する。実自由δ環Lに全深さ0関係を課した通常商を、
変数交換と既存monicPowerFamilyPresentationEquivにより、B=A[Z_(s,n)]上で
X_s^p=C d Z_(s,0)+C b_sを課した既存MonicPowerFamilyCoverと同型にする。
Bから実商への具体的な係数射と両立する代数同型・忠実平坦性を公開する。
任意σ・任意d・零環を含め、p正則性・ghost・完備性は要求しない。
rawδ包全体や導来完備化をこの深さ0通常商と同一視せず、完全化後CFFは別工程とする。
共通ファイル・CLMST・共有監査は編集しない。

上記深さ0通常商では、元のA作用と自由δ座標係数B作用の塔を標準射で確認し、
通常多項式環Bの忠実平坦性と合成して、元のA上の忠実平坦性も同じBS専用モジュールで証明する。
A作用は既存の多項式・通常商の作用を保つ。

## B4-6：一般d根添加の全深さ0通常商の実表示と忠実平坦性（2026-10-15）

DeltaRootFirstEvaluationQuotient.leanで、全深さ0関係の通常商と、自由δ座標を係数とする
既存モニック根添加環との標準環同型を構成した。全深さ0イデアルが既存の
deltaDivisionFiniteRelationIdealの段0と一致することも証明した。
具体的な自由δ座標係数射との両立性・代数同型を証明し、その射の通常忠実平坦性を得た。
さらに元のA作用との標準の塔を確認し、通常多項式環の忠実平坦性と合成して、
元のA作用についても実段0商が忠実平坦であることを証明した。元のA作用は既存作用を保持した。
任意σ・一般d・零環を含み、p正則性・dの正則性・ghost単射・完備性は不要。
13新公開宣言の対象3524ジョブ成功、最終B4全体pure監査1826報告成功、標準3公理のみ。
新sorry・公理・外部引用なし。今回2モジュール計17新公開宣言を全て専用監査で検査した。
今回の平坦性は実段0の通常商に関する証明であり、全δ関係を課したraw包や
実導来完備化後のCFFとは同一視しない。G3・G6・G7は共通計画でも未実装のまま。
一般B4全射性は未完成であり、次は段0の忠実平坦性から次の実δ関係の先頭係数の正則性を供給する
有限段の比較を調べ、一般d根添加候補へ進める。共有・CLMST・利用先は編集していない。
