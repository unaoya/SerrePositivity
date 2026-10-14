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
