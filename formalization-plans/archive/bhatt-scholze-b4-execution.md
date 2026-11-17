# B4：semiperfectoid環のperfectoid化の全射性

> **アーカイブ（2026-10-18）**：B4（Thm 7.4 の全射性）は 2026-10-16 に引用なしで完了。数学は解説の `par:bs-thm74`、原典の依存関係と経路の差は [BS 主計画](../bhatt-scholze/notes/bhatt-scholze.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


2026-10-16。B4は引用なしで完成。正本は`formalization-plans/bhatt-scholze/notes/bhatt-scholze.md`、
担当・待合せは`clmst.md` §0.2。B3の一般存在・普遍性も証明済み。
後半の各記録は各時点の検証結果であり、過去の未完成・待合せ状況を含む。

## 現在の完了点（2026-10-16）

公開一般定理は`SemiperfectoidSurjectivity.lean`の
`surjective_of_isPerfectoidization_of_semiperfectoid_quotient`。
任意perfectoid環R、全射q:R→S、S自身の導来p完備性、任意f:S→CとIsPerfectoidization p fから全射性を証明した。
Sのp正則性・有限性・古典的完備性は追加せず、零環・一般pねじれ商・任意核を含む。
B3と合成した`exists_surjective_perfectoidization_of_semiperfectoid_quotient`も証明済み。

根prism台環候補の(p,d) CFFから正則生成元商の実還元を経て、既存perfectoid候補の標準基底射のp CFFを証明した。
任意根族の具体的perfectoid拡大と互換根を供給し、元の核全体を添字として既証の降下を適用した。
一般perfectoid源への移送は既存Fontaine/完全prism商表示と全射qの合成で行った。
G7-Finset・G9・G11とその他共通基盤は受領した既存APIを使用した。

`Inputs/SemiperfectoidSurjectivity.lean`の旧B-S sorryを同じ署名の証明へ置換した。
旧任意普遍対象への移送APIとCLMST/CyclicPerfectoidizationも再ビルド4363ジョブ成功。
pure B4監査は旧B-S存在・旧移送APIまで含む2560宣言で成功し、標準3公理以外・sorryAxなし。
一般定理から旧B-S入力へのimportもなく、循環依存なし。

André引用に相対的な既存成果は条件付きのまま保持するが、このB4の証明には依存しない。
整代数perfectoid化のB-I/B6引用は維持し、B5は別工程である。

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

### 次工程の登録：一般dの次δ関係の正則性と根添加の第1段

BS専用DeltaDivisionFiniteRelationsRegular.leanを新設する。既存一元p版の一次多項式補助証明を
同モジュールへ移し、任意除数d・任意元族・任意sについて、前段商上のφ^(N+1)(d)の係数像の
正則性から次の実反復δ関係の正則性を証明する。初期有限商・後続変数表示は既存APIを使う。
最初の関係についてもdの正則性による判定を公開する。既存DeltaPDivisionFiniteRelationsRegularは
新一般判定の特殊化へ整理し、公開型を維持する。一般的な共通平坦性判定は新設しない。
BS専用DeltaRootSecondRelationRegular.leanで、前ターンの深さ0商のA上忠実平坦性から
φ(d)の係数像の正則性を供給し、φ(d)がAで正則なら任意根添字の深さ1の実δ関係が
全深さ0商上で非零因子であることを証明する。正の全深さの列の正則性とは区別する。
共有・CLMSTファイルは編集しない。全新公開宣言をBS専用監査へ追加する。

## B4-6：一般dの先頭係数から次δ関係への正則性判定（2026-10-15）

DeltaDivisionFiniteRelationsRegular.leanで、前段実関係商上のφ^(N+1)(d)の係数像が正則なら、
任意添字sの次の実反復δ関係がその商上で非零因子となる判定を証明した。
先頭係数の正則性を初期有限関係商へ降ろす補題と、d正則性による最初の実関係の判定も公開した。
σの有限性・一元性・p正則性・ghost単射・完備性は不要。係数像の正則性という入力は明示して保持する。
既存DeltaPDivisionFiniteRelationsRegularの一次多項式補助証明を新一般モジュールへ移し、
旧一元p版の公開型を維持したまま一般判定の特殊化へ整理した。重複補助証明は除いた。
一般版3214ジョブ、既存p版3764ジョブ、B4全import依存4280ジョブ成功。
警告は既存のLocalFlatnessCriterion長行、DerivedTensorPentagon設定コメント、
DeltaPDivisionSequentialKoszulUnitのhaveI形式のみ。B4全体pure監査1829報告成功、標準3公理のみ。
3新公開宣言を監査済み。新sorry・公理・引用なし。一般CFF・B4全射性は未完成のまま保持する。

## B4-6：一般d根添加の実深さ1関係と完全prismへの適用（2026-10-15）

DeltaRootSecondRelationRegular.leanで、前ターンの段0商の元のA上の忠実平坦性を使い、
φ(d)がA上で正則なら、全深さ0の実関係商上で次関係の先頭係数像も正則となることを証明した。
一般判定へ適用し、任意の根添字sの実深さ1δ関係がこの段0商上で非零因子となる。
さらに完全δ環ではdの正則性からφ(d)の正則性を既存Equiv判定で供給した。
具体的な完全OrientedPrismの指定生成元に適用する公開入口も証明し、追加の係数正則性を不要にした。
有限σ・p正則性・ghost単射は不要。対象3572ジョブ成功、B4全体pure監査1833報告成功、標準3公理のみ。
4新公開宣言を全て専用監査で検査し、新sorry・公理・引用なし。Andréにも依存しない。
この成果は各深さ1関係の非零因子性であり、複数の深さ1関係の列の正則性や
全δ深さのKoszul分解・Tor消滅・完備化後CFFを結論しない。一般B4全射性は引き続き未完成。
次はこの実反復δ関係の正則性を、実評価関係列・有限源商のTor計算へ接続する。

### 次工程の登録：一般dの反復δ関係から評価関係への正則性移送

BS専用DeltaDivisionFiniteEvaluationRegular.leanを新設する。既存p版にある一般の
有限評価イデアルの後続段公式を同名・同型で移し、一元添字・任意d・任意元族について、
有限評価列の生成イデアルと既存有限反復δ関係イデアルの一致、および前段商上の次の
反復δ関係の正則性から次の評価関係への正則性移送を証明する。
旧DeltaPDivisionFiniteEvaluationRegularの公開APIは一般版の特殊化へ整理し重複証明を除く。
BS専用DeltaRootFirstTwoEvaluationKoszul.leanで、完全prismの生成元による一元根添加について、
既存の深さ0・深さ1の実正則性を組み合わせ、実評価関係の深さ≤1列の弱正則性・Koszul分解と
実自由δ射に沿う対応する有限源グラフ商の正次数Tor消滅を証明する。
任意個の根の全深さや全評価環へのTor移送・CFFをこの一元有限段から結論しない。
共通ファイル・CLMST・共有監査は編集せず、全新公開宣言をBS専用監査へ追加する。

## B4-6：一般dの有限評価関係への正則性移送（2026-10-15）

DeltaDivisionFiniteEvaluationRegular.leanへ既存の一般有限評価イデアルの後続段公式を同名・同型で移し、
一元添字・任意除数d・任意入力aの有限評価列の生成イデアルと実有限δ関係イデアルの一致を証明した。
前段商で次の実反復δ関係が非零因子なら、次の実評価関係も非零因子となる移送を一般化した。
既存DeltaPDivisionFiniteEvaluationRegularの公開型を維持し、一般版の特殊化へ整理して重複証明を除いた。
p正則性・ghost単射・完備性はこの移送に不要。一般版3519ジョブ・旧p版3769ジョブ、
B4全監査import依存4282ジョブ成功。既存3種の警告のみ。B4全体pure監査1835報告成功、標準3公理のみ。
同名で移した既存1宣言・新2宣言を専用監査で検査済み。新sorry・公理・引用なし。
この移送だけから全δ深さの正則性を主張せず、具体的な実δ関係の証明を供給して利用する。
一般CFFとB4全射性は未完成として保持する。

## B4-6：一元根添加の深さ≤1評価Koszul分解と実有限源Tor（2026-10-15）

DeltaRootFirstTwoEvaluationKoszul.leanで、φ(d)が元の係数環A上で正則なら、
一元根添加の実自由δ環上の深さ0・1の評価関係列が弱正則であり、
その実Koszul複体が実通常商の分解を与えることを証明した。
既存の深さ0正則性、深さ1反復δ関係の非零因子性、一般d評価関係への移送を合成した。
さらに対応する実自由δ射に沿う深さ≤1有限源グラフ商の全正次数Tor消滅を証明した。
完全OrientedPrismの指定生成元を使うKoszul分解とTor消滅の公開入口では、
φ(d)正則性を追加仮定せず、prismの指定生成元正則性とδ構造の完全性から供給する。
5新公開宣言の対象3574ジョブ成功、最終B4全体pure監査1840報告成功、標準3公理のみ。
新sorry・公理・引用なし。p正則性・ghost単射・古典的完備性・Noether性の追加はない。
一元添字[Unique σ]と有限δ深さ≤1を明示する。任意個の根・全δ深さのTorや
全源評価環・実導来完備化後CFFへはまだ拡張していない。一般B4全射性は未完成。
共通G3・G6・G7も共通計画上未完了であり、この成果で解消したとは数えない。
次はより高いδ深さで必要な先頭係数の正則性と、原典の(p,d)完備化後の比較を確認する。

### 次工程の登録：一般dの最初のδ関係のmod(p,d)正則性

BS専用DeltaDivisionFirstJetResidueRegular.leanを新設する。一般D,d,aについて、
L=A{Z}のJ=(p,Cd)+I_0による通常商を、A/(p,d,a_s)上の自由変数多項式環と標準同型にする。
その商で最初のδ関係はC(δd) Z_(s,0)^p-C(δa_s)となることを証明し、
δdが指定単元ならモニック冪関係へ移して非零因子性を証明する。
p正則性・d正則性・ghost単射・完備性・有限σは要求しない。
既存の高段mod(p,d)正規化定理へ接続する初期段とし、全有限列や完備化後CFFを先取りしない。
共有・CLMST・共有監査は編集せず、全新公開宣言をBS専用監査へ追加する。

### 次工程の登録：最初のδ関係の有限族のmod(p,d)Koszul分解

BS専用DeltaDivisionFirstJetResidueKoszul.leanを新設する。一般D,d,a、指定単元δdについて、
J=(p,Cd)+I_0の実通常商上で異なる有限添字の深さ1δ関係列が弱正則・Koszul分解となることを証明する。
前工程の標準多項式表示と像公式を用い、既存のモニック根関係の有限族の正則性を移す。
σは任意、有限列の添字単射を明示し、p正則性・ghost・完備性・一元性を要求しない。
全δ深さや全源評価環のTor、完備化後CFFはこの同段有限列からは結論しない。
共有・CLMSTファイルは編集しない。

## B4-6：一般dの最初のδ関係の実mod(p,d)非零因子性（2026-10-15）

DeltaDivisionFirstJetResidueRegular.leanで、J=(p,Cd)+I_0が既存係数イデアル(p,d,a_s)の
自由δ環への拡張に一致することを証明し、その実商をA/(p,d,a_s)上の多項式環と標準同型にした。
実標準商像の公式と、最初のδ関係の像がC(δd)Z_(s,0)^p-C(δa_s)となる公式を証明した。
δdが指定単元なら、その像は単元倍のモニック冪関係であり、元の実初期商上でも非零因子となる。
有限σ・一元σ・p正則性・d正則性・ghost単射・完備性は不要。零商も含む。
6新公開宣言の対象3513ジョブ成功、B4全体pure監査1846報告成功、標準3公理のみ。
全新公開宣言を専用監査で検査済み。新sorry・公理・引用なし。
これは既存の高段mod(p,d)正規化へ接続する初期段であり、全有限列や完備化後CFFはまだ結論しない。
前ターンの通常段0商上のφ(d)正則性を使う経路とは仮定と対象商を区別する。
一般B4全射性は未完成として保持する。

## B4-6：任意添字の最初のδ関係の有限族の実mod(p,d)Koszul分解（2026-10-15）

DeltaDivisionFirstJetResidueKoszul.leanで、指定単元δdの下、全深さ0を課した初期mod(p,d)商上で
異なる有限個の深さ1δ関係の列が弱正則であり、実Koszul複体が実通常商の分解となることを証明した。
前工程の標準多項式同型・像公式と、既存の有限モニック根関係の弱正則性を再利用した。
単独の各関係の非零因子性だけから列の正則性を推論せず、単元倍した有限列の生成イデアルと
前段商の正則性を確認した。σの一元性・有限性、p正則性・ghost単射・完備性は不要。
2新公開宣言の対象3517ジョブ成功、最終B4全体pure監査1848報告成功、標準3公理のみ。
新sorry・公理・外部引用なし。今回2モジュール計8公開宣言を全て専用監査で検査した。
全δ深さ・全源評価環のTor・完備化後CFF・一般B4は未完成として保持する。
著者版Prop3.13（pp.34–35）のφによる底変換、補助φ(y)/p除算包、
分冪包からKos(A;p,y)への検出射を使う順序を再確認した。
従来の境界どおり、通常A/(p,d)の計算だけでは係数側の実Koszul操作を伴う
導来(p,d)完備化後のCFFを結論しない。今後もこの比較を省略せず接続する。
共通G3・G6・G7は共通計画上未完了のまま。共有・CLMST・利用先は編集していない。

### 次工程の登録：一元一般dの全有限δ列の実mod(p,d)Koszul分解

BS専用DeltaDivisionFiniteResidueKoszul.leanを新設する。L=A{Z}、B=(p,Cd)、
R=L/Bとし、一元添字の実反復δ列の像の全有限prefixを扱う。
そのprefixの生成イデアルとI_N.map(L→R)の一致、標準二重商比較を証明する。
指定単元δdによる初期段と既存の高段正規化定理を合成し、実前段商上で次の関係の正則性を証明する。
初項のR上正則性を明示入力として、全有限prefixの弱正則性・Koszul分解を証明する。
高段の既存APIのp正則性・ghost単射は明示仮定として保持し、未受領G4等を解消したとはしない。
これは実mod(p,d)商上の全有限列の結果であり、導来(p,d)完備化後CFFとは区別する。
共有・CLMST・共有監査は編集せず、全新公開宣言をBS専用監査へ追加する。

### 次工程の登録：根添加の全有限δ深さの実mod(p,d)Koszul分解

BS専用DeltaRootFiniteResidueKoszul.leanを新設する。一般D,d,bの根用多項式δ環について、
最初の根除算関係がmod(p,Cd)で非零因子であることを、既存の係数商・多項式商同型と
任意係数変更後のモニック根関係正則性から証明する。この初項の証明にはp正則性・ghost・完備性を要求しない。
一元添字の全有限反復δ列のmod(p,d)Koszul分解へこの初項を供給する。
高段に必要な元のAのp正則性、自由δ環上のghost単射、指定単元δdは明示入力とする。
共有・CLMSTファイルは編集せず、全新公開宣言をBS専用監査へ追加する。

## B4-6：一般d一元反復δ列の全有限深さの実mod(p,d)Koszul分解（2026-10-15）

DeltaDivisionFiniteResidueKoszul.leanで、mod(p,d)で有限δ関係を課した実二重商と
元の自由環の実有限剰余商の標準比較・代表元公式を構成した。
一元有限δ列の像の生成イデアルが既存有限関係イデアルの像に一致することを証明した。
初期段の指定単元δdによる正則性と既存の高段正規化を合成し、すべての有限前段で
次の実関係の像が非零因子になることを証明した。初項の正則性を明示入力として、
実mod(p,d)反復δ列の全有限prefixの弱正則性・実Koszul分解を証明した。
一元性、基底・自由δ環のp正則性、自由δ環のghost単射、指定単元δdは明示して保持する。
根添加への初項供給は次工程であり、この一般補題の初項仮定を証明済みとはしない。
6新公開宣言の対象3749ジョブ成功（共有の既存長行警告のみ）、B4全体pure監査1854報告成功、標準3公理のみ。
全新公開宣言を専用監査で検査済み。新sorry・公理・引用なし。
実mod(p,d)通常商の分解であり、係数側の実Koszul操作を伴う導来完備化後CFFとは区別する。
一般B4全射性は未完成として保持する。

## B4-6：一元根添加の全有限δ深さの実mod(p,d)Koszul分解（2026-10-15）

DeltaRootFiniteResidueKoszul.leanで、一般dの最初の根除算関係のmod(p,d)正則性を証明した。
根用多項式係数の(p,Cd)商と、自由δ環の(p,C(Cd))商を既存の係数商同型で表示し、
係数変更後もモニック根関係が非零因子であることと、通常多項式環の平坦性を使った。
この初項には一元性・p正則性・ghost単射・完備性は不要。
一元添字の一般全有限列の定理へ初項を供給し、根添加の任意有限δ深さNについて
実mod(p,d)反復δ関係のKoszul複体が実通常商の分解となることを証明した。
高段に必要な元のAのp正則性、根用多項式δ環の自由δ環上のghost単射、指定単元δdを明示入力として保持する。
多項式係数環と自由δ環のp正則性はAのp正則性から供給し、追加の仮定にはしなかった。
2新公開宣言の対象3758ジョブ成功（共有の既存長行警告のみ）、最終B4全体pure監査1856報告成功、標準3公理のみ。
新sorry・公理・引用なし。今回2モジュール計8新公開宣言を全て専用監査で検査した。
これは任意有限δ深さの通常mod(p,d)計算であり、全源評価環のTor・係数側Koszulとの実導来比較・
完備化後CFFの完成ではない。共通G3・G6・G7は共通計画上も未完了として保持する。
一般B4全射性は未完成。次はこの全有限反復δ列の分解を、実自由δ射の評価関係列の
mod(p,d)分解および有限源商の実Torへ移す比較を進める。共有・CLMST・利用先は編集していない。

### 次工程の登録：通常環射後の評価関係正則性と実残余Tor

BS担当の既存DeltaDivisionFiniteEvaluationRegular.leanで、前段I_Nを消す任意の通常環射qについて
q(g_(N+1))正則性からq(h_(N+1))正則性への移送を公開し、従来の通常商版を特殊化へ整理する。
既存DeltaRootFiniteResidueKoszul.leanでは全有限列の弱正則性も公開し、既存Koszul入口をその結果へ整理する。
BS専用DeltaDivisionMappedEvaluationKoszul.leanを新設し、一元添字の任意通常環射q後で
反復δ列・評価列の各有限prefixの生成イデアルがI_N.map qとなることを証明する。
全有限反復δ列の弱正則性から全有限評価列の弱正則性・実Koszul分解へ移す。
BS専用DeltaRootFiniteResidueSourceTor.leanを新設し、この一般比較と既存の根添加mod(p,d)分解を合成して
任意有限δ深さの評価Koszul分解、実射q_mod(p,d)∘αに沿う実有限源グラフ商のTor比較・正次数消滅を証明する。
元のAのp正則性、自由δ環のghost単射、指定単元δdを保持する。全源への移行や実導来完備化後CFFは別工程。
共通・CLMST・共有監査は編集せず、全新公開宣言をBS専用監査へ追加する。

## B4-6：任意通常射後の評価関係正則性と根添加全有限列の弱正則性（2026-10-15）

既存DeltaDivisionFiniteEvaluationRegularで、I_Nを消す任意通常環射qの下で
q(g_(N+1))の正則性からq(h_(N+1))の正則性を得る移送を証明した。
対象環のδ構造・完備性・p正則性・ghostは要求しない。既存通常商版はその特殊化へ整理し公開型を維持した。
既存DeltaRootFiniteResidueKoszulでは、根添加の全有限mod(p,d)反復δ列の弱正則性を公開し、
既存のKoszul分解入口をその弱正則性から得る形へ整理した。高段の明示入力は変更していない。
新2公開宣言を含むB4全import依存4287ジョブ成功、既存3種の警告のみ。
B4全体pure監査1858報告成功、標準3公理のみ。新sorry・公理・引用なし。
全有限実評価列への移送に用いる。全源Tor・完備化後CFF・一般B4の完成とは区別する。

## B4-6：通常射後の全有限反復δ列から実評価列へのKoszul分解の移送（2026-10-15）

DeltaDivisionMappedEvaluationKoszul.leanで、一元添字・任意通常環射qの下、反復δ列と評価列の
各有限prefixの生成イデアルが同じ実I_N.map qに一致することを証明した。
全有限反復δ列の弱正則性を仮定し、各前段商に対して任意通常射版の次関係の正則性移送を適用して、
全有限評価列の弱正則性と実Koszul分解を証明した。対象環のδ構造・完備性は要求しない。
4新公開宣言の対象3520ジョブ、および具体的根Torへの適用を含む3761ジョブ成功。
自身の長行警告を修正済みで、後者の警告は共有の既存長行のみ。
B4全体pure監査1862報告成功、標準3公理のみ。新sorry・公理・引用なし。
全源評価環や完備化後CFFをこの有限列の移送から結論しない。一般B4は未完成として保持する。

## B4-6：一般d根添加の全有限残余評価列と実有限源商のTor消滅（2026-10-15）

DeltaRootFiniteResidueSourceTor.leanで、一元根添加の任意有限δ深さNについて、
実自由δ射の評価関係のmod(p,d)像が実Koszul分解を与えることを証明した。
実自由δ射αと実mod(p,d)商射qの合成q∘αに沿う、源の深さ≤Nグラフ関係による
実通常商のTorを、その残余評価Koszulホモロジーと同型にした。
この比較自体はp正則性・ghost単射・指定単元を仮定せず、源の既存グラフKoszul分解から得た。
既存高段計算の明示入力（元のAのp正則性、根用多項式δ環の自由δ環上ghost単射、指定単元δd）の下で
全有限深さN・全正次数のこの実Torが零となることを証明した。
3新公開宣言の対象3761ジョブ成功（共有の既存長行警告のみ）、最終B4全体pure監査1865報告成功、標準3公理のみ。
今回の新2補題・新4一般比較・新3具体的Tor比較の計9新公開宣言を全て専用監査で検査した。
新sorry・公理・引用なし。Andréに依存しない。
対象の一元性、有限源商、通常mod(p,d)商射との合成を明示する。全源評価環のTor・
係数側Koszul操作を伴う実導来(p,d)完備化後のCFF・一般B4全射性は未完成。
G3・G6・G7も共通計画上未完了として保持する。次はこの一般元族評価の標準有限源商直系と
全評価環との具体的比較を、既存の一元φ/p用余極限APIを再利用・一般化して接続する。
共通・CLMST・共有監査・利用先は編集していない。

### 次工程の登録：任意一元評価入力の有限源商直系と全源Tor移送

BS専用DeltaDivisionSourceEvaluationColimit.leanを新設する。一元添字・任意a:σ→Aの実評価βに対し、
各有限深さグラフ商・標準遷移射・ModuleCatの逐次図式・Aを頂点とする標準余錐を構成し、
実圏論的colimitとの標準比較と代表元公式を証明する。既存φ(y)版の証明を一般化して再利用する。
既存DeltaDivisionSourceFiniteColimitの公開型は維持し、新一般版の特殊化へ整理して重複証明を除く。
BS専用DeltaDivisionSourceEvaluationColimitTor.leanで、任意終域への通常射と標準PreservesColimit入力の下、
全有限源商のTor消滅を全評価環Aへ移す。旧DeltaPDivisionSourceColimitTorもこの一般移送へ整理する。
BS専用DeltaRootResidueSourceColimitTor.leanで、前工程の根添加の実残余有限Tor消滅を供給し、
一般d・一元根添加の全評価環に対する実残余自由δ射の正次数Tor消滅をG7交換入力に相対的に証明する。
G7自体の実装・受領、係数側Koszulとの比較、実導来完備化後CFFの完成とは数えない。
共有・CLMST・共有監査は編集せず、全新公開宣言をBS専用監査へ追加する。

## B4-6：任意一元評価入力の実有限源商直系と全評価環の標準比較（2026-10-15）

DeltaDivisionSourceEvaluationColimit.leanで、任意a:σ→A（σ一元）の評価βに対する有限グラフ商を
既存の任意有限座標商で定義し、実有限イデアルの単調性・評価核の上限表示を証明した。
標準線形遷移射・ModuleCat逐次図式・実評価環Aを頂点とする標準余錐を構成し、
そのIsColimit、実圏論的colimitとの標準同型、各有限商からの標準β射との両立性を証明した。
代数構造は既存deltaDivisionSourceEvaluationAlgebraを再利用し、新たな同等定義を増やしていない。
旧DeltaDivisionSourceFiniteColimitの14公開宣言の型を保ち、一般版のφ(y)特殊化へ整理して重複証明を除いた。
15新公開宣言および既存特殊化3775ジョブ、B4全import依存4290ジョブ成功（既存3種の警告のみ）。
監査が別途の再ビルド中の一時的olean不在に当たったため、全関連ビルド完了後に再実行し、
B4全体pure監査1880報告成功、標準3公理のみ。全新公開宣言を監査済み。新sorry・公理・引用なし。
この成果は標準colimitの具体的普遍性であり、Torとcolimit交換のG7や一般B4の完成とは区別する。

## B4-6：任意一元評価の全源TorへのG7相対的移送（2026-10-15）

DeltaDivisionSourceEvaluationColimitTor.leanで、任意一元評価入力aと任意終域への通常環射φに対し、
具体的な各有限グラフ商の正次数Tor消滅と、この標準逐次図式に対する標準PreservesColimit入力から、
実評価環Aの対応するTor消滅を証明した。BSの具体的図式に対する接続であり、一般G7の再実装ではない。
旧DeltaPDivisionSourceColimitTorの公開型・交換仮定を維持し、既存有限φ/p消滅を一般移送へ供給する特殊化へ整理した。
新1公開宣言の対象3524ジョブ、旧特殊化と後続導来比較3866ジョブ成功（既存共有警告のみ）。
B4全体pure監査1881報告成功、標準3公理のみ。新sorry・公理・引用なし。
PreservesColimit入力自体は未解消として保持し、G7受領・無条件全源Tor・一般B4完成とは数えない。

## B4-6：G7交換入力に相対的な一般d根添加の実残余全源Tor（2026-10-15）

DeltaRootResidueSourceColimitTor.leanで、一般d・一元根添加に対し、実残余自由δ射
q_mod(p,d)∘αに沿う実全評価環の正次数Tor消滅を、標準PreservesColimit入力に相対的に証明した。
前工程で証明済みの全有限源グラフ商のTor消滅を、今回の任意評価入力用の標準colimit比較へ供給した。
環・写像・係数作用は具体的であり、元のAのp正則性、自由δ環のghost単射、指定単元δdと
実有限源商図式に対するG7交換入力を明示する。p,d商にδ構造を仮定していない。
新1公開定理の対象3766ジョブ成功（共有の既存長行警告のみ）。最終B4全体pure監査1882報告成功、標準3公理のみ。
今回3モジュール計17新公開宣言を全て専用監査で検査した。新sorry・公理・引用なし。Andréにも依存しない。
G7入力は未解消であり、G7受領・無条件全源Tor消滅・導来完備化後CFF・一般B4全射性の完成とは数えない。
共通G3・G6・G7は共通計画上も未完了として保持する。次は実残余通常テンソルと既存raw(p,d)商との
標準比較、Torの向きをそろえた実導来係数拡大の次数零比較、係数側Koszul操作との接続を進める。
共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：実残余通常テンソルとraw残余商の標準比較

BS専用DeltaDivisionSourceResidueTensor.leanを新設する。任意D,d,cについて、
自由δ射αの終域Lの(p,Cd)商を実源代数として与え、A_β⊗_P(L/(p,Cd))と既存rawδ包の(p,d)商との
標準環同型・A代数同型を構成する。既存deltaDivisionSourceTensorEquivとMathlibのtensorQuotientEquivを合成し、
イデアル像・純テンソル像の公式を証明する。新たな商・raw包の定義を重複して作らない。
BS専用DeltaRootResidueSourceDerived.leanで、G7交換入力に相対的な根添加全源Tor消滅を使い、
既存Tor対称性・実導来係数拡大の添加写像比較を通じて、実残余評価の導来拡大を
既存raw(p,d)商の次数零対象と比較する。元の係数作用・標準添加写像を保つ比較を目標とする。
元のAのp正則性、ghost単射、指定単元δd、G7入力は保持する。
係数側Koszulとの比較、完備化後CFF、一般B4を完成したとは数えない。
共有・CLMST・共有監査は編集せず、全新公開宣言をBS専用監査へ追加する。

## B4-6：実残余通常テンソルと既存raw(p,d)商の標準比較（2026-10-15）

DeltaDivisionSourceResidueTensor.leanで、任意d,c・任意添字に対し、自由δ射α終域の(p,Cd)商の
実源代数構造を既存の標準商作用から誘導し、その係数射が標準商射とαの合成であることを証明した。
通常pushout比較の下で右因子の(p,Cd)イデアル像がraw包の(p,d)イデアルに一致することを証明し、
既存deltaDivisionSourceTensorEquivとMathlib.tensorQuotientEquivを合成して、
実残余通常テンソルA_β⊗_P(L/(p,Cd))と既存raw(p,d)商の標準環同型を構成した。
純テンソル像の公式と、元の係数A作用を保つ代数同型も証明した。
源作用と標準自己作用が同じ型に現れる箇所では既存作用からのModuleを明示し、係数作用を混同していない。
p正則性・d正則性・ghost・有限性・完備性・G7は不要。6新公開宣言の対象3266ジョブ成功。
B4全体pure監査1888報告成功、標準3公理のみ。新sorry・公理・引用なし。
通常比較であり、Tor消滅や係数側Koszul操作を伴う実導来完備化後CFFはここから結論しない。
一般B4は未完成として保持する。

## B4-6：G7入力に相対的な根添加の実残余導来評価比較（2026-10-15）

DeltaRootResidueSourceDerived.leanで、G7入力に相対的な実残余全源Tor消滅を
既存の共通torCommで対称な向きへ移し、実評価βに沿う実残余終域のscalarExtensionTorVanishingを証明した。
標準残余源作用の通常テンソルと実通常係数拡大との係数同値を構成し、前工程のraw残余商との
標準代数同型を合成した。共通の実導来係数拡大の標準添加写像による比較を使い、
βに沿う実導来係数拡大を、既存raw(p,d)商の次数零対象と係数作用を保って同型にした。
その順射を忘却後の実導来圏で標準添加写像と具体的な残余商比較の合成として明示し、両立性を証明した。
Tor対称性や実導来完備性の同等の一般定義を新設していない。
元のAのp正則性、自由δ環のghost単射、指定単元δd、全正次数のG7交換入力は明示して保持する。
4新公開宣言の対象3770ジョブ成功（共有の既存長行警告のみ）、最終B4全体pure監査1892報告成功、標準3公理のみ。
標準添加写像の式を整える途中に型不一致があり、通常導来圏への忘却を明示して修正後、対象ビルド・全監査を再実行した。
今回2モジュール計10新公開宣言を全て専用監査で検査した。新sorry・公理・引用なし。Andréにも依存しない。
対象はβに沿うこの具体的導来拡大であり、元のAからの係数側Koszul操作を伴う実導来(p,d)完備化後CFFや
一般B4の完成とは区別する。共通G3・G6・G7も共通計画上未完了として保持する。
共通TorFlatBaseChangeVanishing.torModule_quotient_map_subsingletonは、元のAからの自由多項式係数射と
その合成の平坦性から、商基底変更の両因子のTor消滅を供給できる既存APIであることを再確認した。
次はこれを具体的β・α因子へ適用し、既存DerivedBaseChangeRightTensorの両因子のTor仮定を省かずに
係数側Koszul・導来還元との比較へ接続する。共有・CLMST・利用先は編集していない。

### 次工程の登録：自由δ射の両因子の係数商Tor入力

BS専用DeltaDivisionSourceCoefficientTor.leanを新設する。元の係数環Aから自由δ環Lへの係数射Cと
評価β:L→A・自由δ射α:L→Lを使い、任意係数イデアルI⊆Aについて、
q:L→L/I Lに沿うMβとMαそれぞれのscalarExtensionTorVanishingを証明する。
共通torModule_quotient_map_subsingletonとtorCommをそのまま使い、Cの平坦性、β∘C=id、α∘C=Cを具体的に供給する。
(p,d)についてI L=(p,Cd)のイデアル像公式も公開する。p正則性・ghost・G7・完備性は仮定しない。
BS専用DeltaDivisionSourceCoefficientReduction.leanで、この両入力を共通DerivedBaseChangeRightTensorの
実テンソル商基底変更へ供給し、係数作用を保つ具体的比較を公開する。
同等の一般Tor・導来完備性・完備テンソル定義を重複しない。共有・CLMST・共有監査は編集しない。
全新公開宣言をBS専用監査で検査する。導来(p,d)完備化後CFF・一般B4完成とは区別する。

## B4-6：自由δ射の両因子の係数商Tor消滅（2026-10-15）

DeltaDivisionSourceCoefficientTor.leanで、任意係数イデアルI⊆Aについて、
実係数商q:L→L/I Lに沿う、実評価βで作用するAと実自由δ射αで作用する終域Lそれぞれの
scalarExtensionTorVanishingを証明した。共通torModule_quotient_map_subsingletonへ
係数包含Cの平坦性、β∘C=idおよびα∘C=Cの具体的な平坦性を供給し、共通torCommを再利用した。
Torの向きと加群表現の違いは、実際の線形同値とTor関手による比較で整えた。
(p,d)係数イデアルの拡張が自由δ環の(p,Cd)に一致する公式も公開した。
p正則性・d正則性・ghost単射・G7・完備性・Noether性・添字有限性は不要。
3新公開宣言の対象2868ジョブ成功（共有の既存長行警告のみ）、B4全体pure監査1895報告成功、標準3公理のみ。
新sorry・公理・引用なし。両因子のTor入力を実導来商基底変更へ供給するための結果であり、
係数側Koszul複体との同一視・導来完備化後CFF・一般B4全射性はまだ結論しない。

## B4-6：両因子のTor入力を供給した実係数商テンソル比較（2026-10-15）

DeltaDivisionSourceCoefficientReduction.leanで、任意I⊆Aの拡張イデアルJ=I Lについて、
Jのβ像がI、α像がJに一致する具体的な公式を証明した。
共通restrictedDerivedTensorQuotientAlgebraIsoへ前工程で証明済みの両因子の
scalarExtensionTorVanishingを供給し、実自由δ射の二因子の実導来テンソルを
係数商L/Jで実導来還元した対象と、両通常商の残余作用付き実導来テンソルとの標準比較を構成した。
実通常係数拡大の値そのものを用いる加群表示も、共通の右テンソル比較と両因子の添加写像比較から構成した。
α側の残余源作用を標準自己作用へ置き換えていない。一般の導来・完全平坦性の同等定義は新設していない。
p正則性・d正則性・ghost単射・G7・完備性・添字有限性は不要。
4新公開宣言の対象2885ジョブ成功（既存共有警告のみ）、最終B4全体pure監査1899報告成功、標準3公理のみ。
今回2モジュール計7新公開宣言を全て専用監査で検査した。新sorry・公理・引用なし。
この工程は両因子のTor仮定を実際に解消した係数商比較であり、前ターンのG7相対的残余導来評価比較と
接続していく。係数側Koszul複体を通常L/Jへ無条件に置換したものではなく、
導来(p,d)完備化後CFF・一般B4全射性は引き続き未完成。
共通G3・G6・G7は共通計画上未完了として保持する。次はβ・αの商への降下写像を標準射と両立させ、
前工程の実残余導来評価比較とこの二因子の導来還元を接続する。共有・CLMST・利用先は編集していない。

### 次工程の登録：β・αの係数商への標準降下と実還元対象の明示

BS専用DeltaDivisionSourceCoefficientMaps.leanを新設する。任意係数イデアルI、J=I Lについて、
βbar:L/J→A/I、αbar:L/J→L/J、Cbar:A/I→L/Jを既存Ideal.quotientMapで構成し、
標準商代表元・βbar∘q_L=q_A∘β・αbar∘q_L=q_L∘α、βbar∘Cbar=id、αbar∘Cbar=Cbarを証明する。
源商にδ構造を仮定せず、αbarを標準自己作用へ置換しない。
BS専用DeltaDivisionSourceCoefficientQuotients.leanを新設する。既存導来商比較に現れるA/Jβ・L/Jαを
それぞれβbarで作用するA/I・αbarで作用するL/Jと標準代数同型で比較する。
その比較を前工程の実二因子導来還元へ合成し、商への降下写像を明示した標準の実導来同型を公開する。
p正則性・ghost・完備性・G7は仮定しない。共通・CLMST・共有監査は編集しない。
全新公開宣言をBS専用監査で検査し、導来完備化後CFF・一般B4完成とは区別する。

## B4-6：β・α・係数包含の任意係数商への標準降下（2026-10-15）

DeltaDivisionSourceCoefficientMaps.leanで、任意I⊆A、J=I Lについて、既存Ideal.quotientMapを使って
βbar:L/J→A/I、αbar:L/J→L/J、Cbar:A/I→L/Jを構成した。
各標準商代表元の公式、βbar・αbarと標準商射の二つの可換図式、
βbar∘Cbar=idとαbar∘Cbar=Cbarを証明した。商のδ構造やαbarの恒等性は仮定しない。
10新公開宣言の対象2886ジョブ成功（既存共有警告のみ）、B4全体pure監査1909報告成功、標準3公理のみ。
新sorry・公理・引用なし。p正則性・ghost・G7・完備性・添字有限性は不要。
この具体的な降下射を、実二因子の係数商比較の作用の明示へ使う。
一般B4全射性・導来完備化後CFFは未完成として保持する。

## B4-6：実二因子の係数商とβbar・αbar作用を保つ明示的導来比較（2026-10-15）

DeltaDivisionSourceCoefficientQuotients.leanで、βbarが定めるA/Iの源商代数構造と、
αbarが定めるL/Jの源商代数構造を具体的降下射から与えた。
既存の実係数商比較に現れるA/Jβ・L/Jαを、それぞれA/I・L/Jへ標準の商同型で移し、
この比較がβbar・αbarの実源商作用を保つ代数同型となることを証明した。
両代数同型を実導来二因子の係数商比較へ合成し、右辺をβbarで作用するA/Iと
αbarで作用するL/Jの実導来テンソルとして明示した。αbarを標準自己作用へ置き換えていない。
標準商の作用を二重に暗黙推論させず、既存adicQuotientAlgebraによる作用を明示して整えた。
5新公開宣言の対象2887ジョブ成功（既存共有警告のみ）、最終B4全体pure監査1914報告成功、標準3公理のみ。
今回2モジュール計15新公開宣言を全て専用監査で検査した。新sorry・公理・引用なし。
p正則性・ghost・G7・完備性は不要。既存共通のTor・導来基底変更・テンソル定義を再利用した。
共通G3・G6・G7は共通計画上未完了として保持し、導来完備化後CFF・一般B4全射性は未完成。
次は共通boundedAboveDerivedTensorAssociatorで三因子を組み替え、右因子に
boundedAboveDerivedBaseChangeRightTensorNatIsoと証明済みTor消滅を適用する。
これにより、係数商還元を前段で計算した実残余因子とのテンソルへ接続する経路を進める。
任意の新しい投影公式を構築する前に、この既存の結合子・右係数拡大比較で足りる範囲を実装する。
共有・CLMST・利用先は編集していない。

### 次工程の登録：右因子の実係数還元と三因子の結合子による接続

BS専用DeltaDivisionSourceCoefficientRightFactor.leanを新設する。q:L→L/J、ψ=q∘αについて、
前工程のαbar作用付きQ=L/Jの商代数比較とα因子のTor消滅から、
Res_q(Lq Single(Mα))とSingle(Mψ)を標準線形比較で同型にする。
共通の右係数拡大比較によりSingle(Mα)⊗^L QをSingle(Mψ)へ移し、
共通結合子から(Single(Mβ)⊗^L Single(Mα))⊗^L QをSingle(Mβ)⊗^L Single(Mψ)へ比較する。
任意Iについてp正則性・ghost・G7・完備性は不要。
BS専用DeltaRootSourceCoefficientResidue.leanでI=(p,Cd)の根添加に特殊化し、
既存G7相対的残余導来評価比較を合成して、この具体的な係数側実導来還元を既存raw(p,d)商へ接続する。
G7、元のAのp正則性、ghost単射、指定単元δdは後者だけで保持する。
共有・CLMST・共有監査は編集せず、全新公開宣言を専用監査で検査する。
導来(p,d)完備化後CFFや一般B4は未完成として区別する。

## B4-6：右因子の実係数還元と三因子の結合子による比較（2026-10-15）

DeltaDivisionSourceCoefficientRightFactor.leanで、αbar作用付き商をqで係数制限すると
ψ=q∘αの実作用になる標準線形同値を構成した。既存α因子のTor消滅と商比較を使い、
Res_q(Lq Single(Mα))をSingle(Mψ)と標準同型にした。
共通の右係数拡大比較と導来テンソル結合子を合成し、
(Single(Mβ)⊗^L Single(Mα))⊗^L QをSingle(Mβ)⊗^L Single(Mψ)へ比較した。
(p,d)特殊化では商環と作用が同時に変わるため、イデアルを変数とする完全な型族で輸送し、
実商射L→L/(p,Cd)を明示した比較を公開した。p正則性・ghost・G7・完備性・添字有限性は不要。
6新公開宣言の対象2888ジョブ成功（既存共有警告のみ）、B4全体pure監査1920報告成功、標準3公理のみ。
新sorry・公理・引用なし。共通の導来テンソル・結合子・係数拡大・係数制限の既存APIを再利用した。
根添加の既存残余導来評価比較へ合成するための接続であり、一般B4・完備化後CFFの完成ではない。

## B4-6：根添加の実係数還元とraw残余商の導来同型（2026-10-15）

DeltaRootSourceCoefficientResidue.leanで、根添加の具体的な実三因子導来対象を
既存boundedAboveDerivedTensorで定義し、前工程の右因子還元と結合子による比較を
G7入力付きの実残余導来評価比較へ合成した。結果は、実評価βで係数制限した
既存raw(p,d)商の次数零対象との同型である。H0のModuleCat同型と非零次数ホモロジーの
消滅も公開した。raw商の元来の源作用をβによる係数制限作用と混同しない型で記述した。
元のAのp正則性、自由δ環のghost単射、δdを与える指定単元、全正次数の
具体的有限源商図式に対するPreservesColimit入力を明示して保持している。
4新公開宣言の対象3787ジョブ成功（共有の既存警告のみ）、B4全体pure監査1924報告成功、
標準3公理のみ。新sorry・公理・引用なし。共通の導来テンソル・係数拡大・係数制限・
H0比較を再利用した。G7の実装受領、係数側Koszul複体との同一視、導来完備化後CFF、
一般B4全射性の完成とは数えない。G3・G6・G7は送信・受領済みであり重複送信しない。
次は係数側Koszul還元との比較に必要なp,dの正則性条件を確認し、この具体的な残余同型を
完備化・平坦性工程へ渡す。共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：実商環上の根添加導来還元

BS専用DeltaRootSourceQuotientDerived.leanを新設する。
前工程の三因子対象を、実商射q:L→L/(p,C(Cd))に沿う実導来基底変更の
係数制限と共通の右テンソル比較で同定する。raw残余商上のL作用はβを経由するため、
この作用のqへの降下射を明示する。係数制限のホモロジー比較から実商環上の非零次数消滅を
反映し、H0比較の線形性をqの全射性で商環上へ昇格する。
G7交換入力・p正則性・ghost単射・指定単元δdは保持し、d mod pの正則性は追加しない。
Koszul還元との無条件な同一視や実完備化後CFFの完成とは区別する。
全公開宣言を専用監査へ登録し、共有・CLMST・共有監査は編集しない。

## B4-6：実商環上の導来還元と作用を保つH0比較（2026-10-15）

DeltaRootSourceQuotientDerived.leanで、実二因子導来テンソルを実商射
q:L→Q=L/(p,C(Cd))で基底変更した実Q上の対象を定義した。
raw残余商への作用射はβ・既存raw係数射・残余商射の合成をqへ降下して与え、
代表元公式と、qで係数制限した作用が既存β作用に一致する加群同型を証明した。
共通の右テンソル比較で実Q上の還元と前工程の三因子対象を結び、
係数制限とホモロジーの比較から実Q上の全非零次数消滅を証明した。
H0は、qの全射性を使ってL線形同型を実Q線形同型へ昇格し、raw残余商と比較した。
商の作用の一致には通常のAlgebra.smul_defを使い、raw商の通常作用と明示した降下作用を照合した。
元のAのp正則性・ghost単射・指定単元δd・具体的G7交換入力を保持し、d mod pの正則性は追加しない。
8新公開宣言の対象3788ジョブ成功（共有の既存警告のみ）、B4全体pure監査1932報告成功、
標準3公理のみ。新sorry・公理・引用なし。共有・CLMST・利用先・共有監査は編集していない。
この工程は通常商への実導来基底変更を商環上で計算したものであり、
任意(p,d)のKoszul還元への無条件な置換・完備化後CFF・一般B4完成を意味しない。
次は実Q上のH0を元の係数商A/(p,d)へ制限し、既存raw残余商の忠実平坦性へ接続する。

### 次工程の登録：実商還元のH0と元の係数商上の忠実平坦性

BS専用DeltaRootSourceQuotientFlat.leanを新設する。
A/(p,d)→Qの標準二重係数包含を降下し、Q→raw残余商との合成が既存の
標準raw係数射と一致することを商代表元で証明する。
その作用比較を実Q上のH0同型に合成し、実導来商還元のH0をA/(p,d)上の
標準raw残余商と線形同型にし、既存raw残余商の忠実平坦性を移す。
G7・p正則性・ghost単射・指定単元を保持し、一般Koszul還元や完備化CFFと区別する。
公開宣言を専用監査で検査し、共有・CLMST・共有監査は編集しない。

## B4-6：実導来商還元のH0を元の係数商上の忠実平坦性へ接続（2026-10-15）

DeltaRootSourceQuotientFlat.leanで、元のA/(p,d)から実源商Qへの二重係数包含を降下した。
商代表元の公式と、Qからraw残余商への作用射との合成が既存raw標準係数射に一致する図式を公開した。
この作用図式を実Q上のH0同型へ適用し、既存raw残余商とのA/(p,d)線形同値を構成して、
既存のraw残余商の忠実平坦性を実導来商還元のH0へ移した。
二重多項式環のp正則性は元のAのp正則性から平坦性により内部供給した。
公開定理は具体的な実導来基底変更のH0を対象とし、ghost単射・指定単元δd・G7交換入力は保持する。
d mod pの正則性、Noether性、有限生成性は追加していない。
4新公開宣言の対象3789ジョブ成功（共有の既存警告のみ）、B4全体pure監査1936報告成功、
標準3公理のみ。新sorry・公理・引用なし。二工程の自分の検証済み変更だけを個別コミットした。
この忠実平坦性は通常商への実導来還元のH0についての結果であり、一般の係数Koszul還元への
比較・実導来完備化後CFF・一般B4全射性は未完成。共通G3・G6・G7の実装受渡しも未完了として保持する。
次は源側の係数Koszul還元との比較と完備化単位の整合を進める。一般prismでは(p,d)商を
無条件にKoszul複体へ置換せず、必要な比較・条件を明示する。共有・CLMST・利用先は編集していない。

## 共通基盤要求G4・G8の送信記録（2026-10-15）

ユーザーの明示許可「2件を送ってよい」に基づき、CLMSTチャット
（01a13993-b4ee-7a10-8441-7d21224139d7、local）へG4とG8の正確な仮定・結論、
追加しない仮定、利用工程、既存APIの不足、待つ箇所と独立作業を送信した。
ツールの成功を確認した。G4はp乗算単射下のWitt ghost単射、G8は実導来完備化と
係数制限の自然同型および標準単位との両立である。上の「未送信」「未許可」は
この送信前の状態を記したものであり、本記録で更新する。
送信成功を実装受領・依存解消とは扱わず、一般共通補題をBSで重複実装しない。
この許可は他の追加要求の送信や共有ファイルの編集へ拡張しない。

### 次工程の登録：実商還元の次数零対象との正規化導来同型

BS専用DeltaRootSourceQuotientSingle.leanを新設する。
実商環Q上で証明済みの全非零次数ホモロジー消滅から標準t構造の次数零集中を得る。
共通normalizedPureHomologyIsoと既存実Q線形H0同型を合成し、実導来商還元そのものを
raw残余商のsingle対象へ比較する。H0へ施すと前工程の具体的H0同型になる正規化公式も証明する。
G7入力・p正則性・ghost単射・指定単元δdを明示し、一般Koszul還元・完備化CFFと区別する。
共通の純対象比較を重複定義せず再利用し、全公開宣言をBS専用監査へ登録する。

## B4-6：実商還元そのものとraw商の次数零対象の正規化比較（2026-10-15）

DeltaRootSourceQuotientSingle.leanで、実Q上の全非零次数ホモロジー消滅から
標準t構造のIsGE 0とIsLE 0を証明した。共通normalizedPureHomologyIsoを再利用し、
既存実Q線形H0同型と合成して、実導来商還元そのものを作用付きraw残余商の
single対象と実Q上で同型にした。その同型にH0を施し標準single-H0比較を合成すると、
前工程の具体的なQ線形H0同型に一致する正規化公式も公開した。
一般の純対象比較・single・導来テンソル・ホモロジーの同等定義は新設していない。
元のAのp正則性、ghost単射、指定単元δd、具体的G7交換入力を保持し、d mod p正則性は追加していない。
4新公開宣言の対象3791ジョブ成功（共有の既存警告のみ）、B4全体pure監査1940報告成功、
標準3公理のみ。新sorry・公理・引用なし。共通側へ許可済みのG4・G8は送信成功を記録したが、
実装受領・依存解消とは数えない。一般Koszul還元との比較、完備化後CFF、一般B4全射性は未完成。
次は二重多項式源Lから元の係数環Aへ実対象を制限し、A/(p,d)への実導来還元との比較へ進む。
源LがA上自由であることを使う射影モデルの係数制限から準備し、一般の完備化交換G8は共通側を待つ。

### 次工程の登録：二重多項式源の射影モデルの元の係数環への制限

BS専用DeltaRootSourceCoefficientModels.leanを新設する。
具体的源L=MvPolynomial (σ×ℕ) (MvPolynomial σ A)の二重係数包含A→Lに沿い、
L加群の射影性がAへ制限して保たれることを、自由加群の直和因子表示とLのA自由性から証明する。
その結果を既存BoundedAboveDerivedModelへ供給し、源L上の任意の明示した射影モデルを
実係数制限対象のA上の射影モデルへ変換する。源の具体的係数包含・環・モデルを保持し、
一般の共通導来圏や完備化の同等定義は新設しない。
このモデルをA/(p,d)で基底変更する比較を公開し、実源商Q上の比較との接続の準備とする。
G7や正則性をこの準備自体には仮定しない。共有・CLMST・共有監査は編集しない。

## B4-6：実源の射影モデルの元の係数環への制限（2026-10-15）

DeltaRootSourceCoefficientModels.leanで、具体的な二重多項式源LのA上の自由性を使い、
任意のL上の射影加群を実係数包含A→Lで制限しても射影的となることを証明した。
共通Module.projective_def'の自由加群の直和因子表示とModule.Projective.of_splitを再利用し、
実制限加群と通常のFinsupp加群の作用をAlgebra.smul_defで照合した。
指定したL上のBoundedAboveDerivedModelを、実A係数制限対象のA上の射影モデルへ変換し、
元の係数環の任意イデアルIでの実導来還元をその具体的モデルの通常基底変更で計算する比較を公開した。
p正則性・d正則性・δ構造・ghost・G7・完備性はこの準備に不要。
3新公開宣言の対象3792ジョブ成功（共有の既存警告のみ）、B4全体pure監査1943報告成功、
標準3公理のみ。新sorry・公理・引用なし。共通の導来モデル・係数制限・基底変更を再利用した。
共通計画にG4・G8の受領済み・未実装を確認した。実装受渡しやG7解消とは数えない。
次は通常加群の商基底変更と係数制限の比較を具体的源について構成し、今回の射影モデル比較に適用する。
Koszul還元への置換・完備化後CFF・一般B4全射性は未完成。共有・CLMST・利用先は編集していない。

### 次工程の登録：実源の通常加群の係数商比較

BS専用DeltaRootSourceCoefficientSquare.leanを新設する。
I⊆A、J=I Lについて、L加群MのA係数制限をA/Iで還元した加群と、
MをL/Jで還元してA/Iへ制限した加群を標準商写像を保って比較する。
既存quotientModuleFunctor、quotientScalarExtensionIso、adicQuotientAlgebraを再利用し、
拡張イデアルの作用部分加群の係数制限を既存restrictScalars_map_smul_eqで比較する。
通常加群比較の自然性を証明して複体へ適用できる形にする。
源Lの具体的二重多項式構造は保ち、一般の共通導来基底変更関手を重複定義しない。
G7・δ・正則性・完備性は不要。全公開宣言を専用監査し、共有・CLMST・共有監査は編集しない。

今回の係数商比較工程の具体化：上の通常加群自然同型を既存quotientScalarExtensionIsoで
実extendScalarsの自然同型へ移し、項ごとの複体比較を構成する。
前工程のA制限射影モデルと合成して、元のA/Iに沿う実導来還元と
実源商L/I Lに沿う還元のA/I係数制限を、具体的源の任意射影モデルについて同型にする。
これは新しい一般の導来基底変更関手ではなく、既存の両実関手の具体的源における比較である。

## B4-6：元の係数商と実源商による二つの実導来還元の比較（2026-10-15）

DeltaRootSourceCoefficientSquare.leanで、任意I⊆AとJ=I Lについて、通常加群の
拡張イデアルによる作用部分加群を係数制限し、元のI作用部分加群と同定した。
既存restrictScalars_map_smul_eq・商部分加群の同型・商加群関手を再利用し、
A/Iで還元した実A制限加群と、L/Jで還元してA/Iへ制限した加群を、商代表元を保って比較した。
任意L加群射に対する自然性を証明し、既存quotientScalarExtensionIsoで実extendScalarsの
自然同型へ移して、複体への項ごとの比較を構成した。
前工程のA上の制限射影モデルと共通derivedRestrictScalarsFactorsを合成し、
具体的な源L上の任意実上有界対象と指定射影モデルについて、A/Iでの実導来還元と
L/I Lでの実導来還元をA/Iへ制限した対象との同型を公開した。
Tor消滅、p・d正則性、δ構造、ghost、G7、完備性はこの比較に不要。
7新公開宣言の対象3793ジョブ成功（共有の既存警告のみ）、B4全体pure監査1950報告成功、
標準3公理のみ。新sorry・公理・引用なし。二工程の自分の検証済み変更のみを個別コミットした。
次はI=(p,d)へ特殊化し、I L=(p,C(Cd))と標準係数射の一致を明示して、
証明済みの実源商上のsingle比較・H0忠実平坦性へ接続する。
一般Koszul還元への置換・完備化後CFF・一般B4全射性は引き続き未完成。
共有G4・G8は受領済み・未実装、G3・G6・G7の実装受渡しも未完了として保持する。
共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：(p,d)係数商の実導来比較への特殊化

BS専用DeltaRootSourcePDReduction.leanを新設する。
元のI=(p,d)を二重係数包含A→Lで拡張したイデアルが実KL=(p,C(Cd))に一致することを証明する。
商環と係数射が同時に変わる依存型を全体として輸送し、既存任意Iの実導来比較を
KL・既存deltaRootSourceQuotientCoefficientMapの具体的な型へ特殊化する。
実二因子導来対象のA係数制限を定義し、このA/(p,d)還元を既存実KL上の根添加還元へ結ぶ。
その後G7入力付きsingle比較・H0忠実平坦性を合成する。d mod p正則性は追加しない。
一般Koszul還元・完備化後CFF・一般B4とは区別し、全公開宣言を専用監査する。
共有・CLMST・共有監査は編集しない。

## B4-6：元の(p,d)での実導来還元と実源商の具体的比較（2026-10-15）

DeltaRootSourcePDReduction.leanで、元の(p,d)の二重係数包含に沿う拡張が
実源の(p,C(Cd))に一致することを証明した。商環と係数射が同時に変わるため、
商環・係数射の仮定・比較同型を含む依存型全体を輸送し、一般Iの実導来比較を具体的な型へ特殊化した。
輸送後の標準係数射が既存deltaRootSourceQuotientCoefficientMapと一致することを商代表元で照合した。
実二因子導来対象の元のAへの実係数制限を明示し、そのA/(p,d)実導来還元と、
既存の実源商上の根添加還元をA/(p,d)へ制限した対象との同型を公開した。
この比較自体にはp正則性・d mod p正則性・ghost・G7・完備性を仮定しない。
4新公開宣言の対象3794ジョブ成功（共有の既存警告のみ）、B4全体pure監査1954報告成功、
標準3公理のみ。新sorry・公理・引用なし。既存実導来テンソルモデル・係数制限・基底変更を再利用した。
次はG7入力付きの実源商single比較とH0忠実平坦性を、この元のA上の実還元へ合成する。
一般Koszul還元・実完備化後CFF・一般B4全射性は引き続き未完成。共有・CLMST・利用先は編集していない。

### 次工程の登録：元のA上の実(p,d)還元のraw比較とH0忠実平坦性

BS専用DeltaRootSourcePDResidue.leanを新設する。
実源商上のG7入力付きsingle比較を、前工程の実(p,d)係数還元比較へ合成する。
raw残余商は既存Q作用を既存係数射A/(p,d)→Qで制限した加群として明示し、
元のA上の実導来対象のA/(p,d)還元そのものとの導来同型・H0同型・非零次数消滅を公開する。
さらに係数制限とホモロジーの共通比較を使い、証明済みのH0忠実平坦性を同じ実還元へ移す。
G7・元のAのp正則性・ghost単射・指定単元δdを保持し、d mod p正則性は追加しない。
一般Koszul還元との比較・完備化後CFF・一般B4は別工程とし、全公開宣言を専用監査する。

## B4-6：元のA上の実(p,d)還元のraw比較とH0忠実平坦性（2026-10-15）

DeltaRootSourcePDResidue.leanで、元のAへ実係数制限した根添加二因子対象をA/(p,d)で実導来還元し、
既存実源商上のG7入力付きsingle比較へ接続した。結果は、既存Q作用を標準A/(p,d)係数射で
制限したraw残余商のsingle対象との、実A/(p,d)上の導来同型である。
H0の加群同型と全非零次数消滅も公開した。実係数制限とホモロジーの共通比較を使い、
証明済みの実源商H0の忠実平坦性を、元のA上の実(p,d)還元のH0へ移した。
元のAのp正則性・自由δ源のghost単射・指定単元δd・具体的G7交換入力は明示して保持する。
d mod p正則性、Noether性、有限生成性、古典的完備性は追加していない。
4新公開宣言の対象3795ジョブ成功（共有の既存警告のみ）、B4全体pure監査1958報告成功、
標準3公理のみ。新sorry・公理・引用なし。二工程の自分の検証済み変更だけを個別コミットした。
この結果は元のA上の実導来対象の係数商還元についての結果であり、実完備化後CFF・一般B4の完成ではない。

次の完備化工程では、実商射A→A/(p,d)をA→A/p→A/(p,d)とA→A/d→A/(p,d)へ因数分解し、
既存CompletionQuotientの正則主元の標準単位比較を、それぞれの合成基底変更へ移す経路を調べる。
この経路はp正則性・d正則性を個別に使い、d mod pの正則性は要求しない候補である。
通常extendScalarsCompはMathlibに確認できた。上有界実導来版へのモデル比較と標準単位両立は
未実装として保持し、成立を証明するまで完備化後の結果へ数えない。
一般の共通完備化交換G8は受領待ちとして保持する。共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：prism係数の二段商による実導来基底変更

BS専用PrismaticCoefficientQuotientComposition.leanを新設する。
可換環Aとa,d∈AについてA→A/(a)→A/(a,d)の標準因数分解を構成し、合成が実商射に一致することを証明する。
Mathlib.extendScalarsCompと既存の上有界実導来基底変更の射影モデルを使い、
A/(a,d)での実導来基底変更と二段の実導来基底変更の自然同型を、具体的な係数商に限定して構成する。
一般の新しい導来基底変更関手は定義せず、共有に同じ比較APIがないことを確認した上で既存関手を比較する。
後段で既存CompletionQuotientの正則aの標準完備化単位比較をこの因数分解へ移し、
(a,d)還元後にも完備化単位が同型になることを証明する。d mod a正則性は追加しない。
全公開宣言をBS専用監査に登録し、共有・CLMST・共有監査は編集しない。

## B4-6：標準二段係数商による実導来基底変更の自然比較（2026-10-15）

PrismaticCoefficientQuotientComposition.leanでA→A/(a)→A/(a,d)の標準因数分解を構成し、
合成が実(a,d)商射に一致することを証明した。Mathlib.extendScalarsCompを使って通常の
係数拡大を比較し、複体へ項ごとに適用した。
既存の上有界実導来基底変更の射影モデルを再利用し、実(a,d)基底変更と標準二段商による
実導来基底変更の同型を構成した。任意の実導来射に対する自然性を射影モデル上で証明し、
既存実関手どうしの自然同型として公開した。新しい導来基底変更関手は定義していない。
正則性・Tor消滅・Noether性・完備性・δ・ghost・G7は不要。
7新公開宣言の対象2489ジョブ成功（警告なし）、B4全体pure監査1965報告成功、標準3公理のみ。
新sorry・公理・引用なし。次は標準完備化単位をこの自然比較へ適用し、正則aの完備化が
実(a,d)還元を保つことを証明する。一般B4・完備化後CFFの完成とはまだ扱わない。
共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：正則主元の標準完備化単位の二生成係数商での保存

BS専用PrismaticCoefficientCompletionReduction.leanを新設する。
正則aについて、既存CompletionQuotientのA/(a)での標準完備化単位の同型性と
前工程の二段商の実導来自然同型を合成し、A/(a,d)での実導来還元後にも同じ標準単位が
同型であることを証明する。d mod aの正則性は要求しない。
順序を交換して正則dの場合のd完備化単位も扱い、a,dがそれぞれ正則な場合には、
二つの既存実主元完備化を逐次適用した対象の実(a,d)還元と元の還元を、合成標準単位を保って比較する。
逐次完備化を一般の新しい完備化概念として定義しない。完備性の比較・環候補の接続は別工程とする。
全公開宣言をBS専用監査し、共有・CLMST・共有監査は編集しない。

## B4-6：標準主元完備化単位の実二生成係数商での保存（2026-10-15）

PrismaticCoefficientCompletionReduction.leanで、正則aについて、標準a導来完備化単位が
実(a,d)還元後にも同型になることを証明した。既存CompletionQuotientのA/(a)での結果を、
前工程の二段商の実導来自然同型へ適用した。実比較同型は標準単位の像そのものであり、
その逆射と単位との正確な図式と、既存実関手どうしの自然同型を公開した。
順序を交換して正則dの場合の標準d完備化単位も同じ(a,d)商で保存することを証明した。
a,dがそれぞれ正則なら、二つの既存実主元完備化を順に適用した対象の実(a,d)還元が
元の還元と同型になり、二つの標準単位の合成と両立することも証明した。
d mod a正則性、Noether性、有限生成性、有界ねじれは追加していない。
新しい完備化概念・導来関手は定義せず、既存主元完備化関手をそのまま使った。
7新公開宣言の対象2490ジョブ成功（警告なし）、B4全体pure監査1972報告成功、標準3公理のみ。
新sorry・公理・引用なし。二工程の検証済みの自分の変更のみを個別コミットした。
この結果をp正則・d正則なprism係数環へ適用し、前工程の元のA上の実(p,d)還元の
single比較・H0忠実平坦性を、逐次p,d完備化後の実還元へ移すのが次の工程である。
逐次主元完備化と原典(p,d)完備化との比較・環としてのH0候補との接続・完備化後CFF自体・一般B4は
未完成として保持し、共通G8の実装受領とも区別する。共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：具体的根添加対象の逐次主元完備化後の係数商還元

BS専用DeltaRootSourceIteratedCompletionResidue.leanを新設する。
元のA上の実根添加対象に、既存のp完備化・d完備化をこの順に適用した具体的対象を明示する。
元のAのp正則性とd正則性を個別に仮定し、前工程の標準単位付き係数商比較を適用する。
G7入力付きの未完備実還元のraw single比較、非零次数消滅、H0忠実平坦性を逐次完備化後へ移す。
合成標準単位がraw比較へ送られる正確な図式も公開する。d mod pの正則性は要求しない。
逐次主元完備化を原典(p,d)完備化や既存環候補と同一視せず、その比較・離散性・環構造との接続は別工程とする。
全公開宣言をBS専用監査し、共有・CLMST・共有監査は編集しない。

## B4-6：具体的根添加対象の逐次主元完備化後の実(p,d)還元（2026-10-15）

DeltaRootSourceIteratedCompletionResidue.leanで、元のA上の実根添加対象に、既存のp主元完備化、
d主元完備化を順に施した具体的対象を明示した。p正則性・d正則性を個別に仮定して、
標準単位付きの実(p,d)還元比較を適用し、未完備の実還元と同型にした。
G7入力付きの既存raw single比較を合成し、合成標準単位の実還元が未完備側のraw比較へ
送られる正確な図式を公開した。全非零次数ホモロジー消滅とH0のA/(p,d)上の忠実平坦性も移した。
自由δ源のghost単射・指定単元δd・具体的G7交換入力は保持し、d mod p正則性は仮定しない。
7新公開宣言の対象3804ジョブ成功（共有の既存警告のみ）、B4全体pure監査1979報告成功、標準3公理のみ。
新sorry・公理・引用なし。既存の実完備化・導来基底変更・標準単位・ホモロジー比較を再利用した。
逐次対象の二方向の導来完備性、原典の(p,d)完備化との比較、環H0候補との接続、離散性とCFF自体、
一般B4全射性は別工程として保持する。共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：具体的逐次対象の両座標の導来完備性

BS専用DeltaRootSourceIteratedCompletionComplete.leanを新設する。
既存の実p完備化・d完備化の合成で与えた根添加対象について、p方向とd方向のIsCompleteを証明する。
d方向は既存主元完備化の完備性を使う。p方向はp完備化した対象の代表複体を取り、
dの冪の各Koszul錐がp完備であることを既存の錐に関する閉性で示し、
既存の直積・ホモトピー逆極限に関する完備性から結論する。
一般の完備化交換G8や新しい完備化概念は実装せず、既存閉性を具体的根添加対象へ供給する。
正則性・ghost・G7を完備性自体には仮定しない。環構造・離散性・原典との比較は別工程とする。
全公開宣言を専用監査し、共有・CLMST・共有監査は編集しない。

## B4-6：具体的逐次根添加対象のp・d両方向の実導来完備性（2026-10-15）

DeltaRootSourceIteratedCompletionComplete.leanで、同じ具体的逐次対象について、p方向とd方向の
既存IsCompleteを証明した。d方向は既存の実主元完備化の完備性を直接再利用した。
p方向は実p完備化対象の代表複体を取り、dの冪の各Koszul錐がp完備であることを
既存isComplete_Q_mappingConeで示し、既存の直積とホモトピー逆極限の完備性を使って結論した。
代表複体上の計算を既存derivedComplexCompletionComparisonで元の実対象へ戻した。
この二方向完備性自体にはp正則性・d正則性・ghost・G7・Noether性・古典的完備性は不要。
2新公開宣言の対象3805ジョブ成功（共有の既存警告のみ）、B4全体pure監査1981報告成功、標準3公理のみ。
新sorry・公理・引用なし。一般の新しい完備化概念や係数制限交換G8を定義していない。
前工程の明示仮定下の実(p,d)還元の次数零集中・H0忠実平坦性と、今回の無条件な二方向完備性を
同じ対象に供給できた。離散性・元の環H0候補や原典の完備化との比較・完全忠実平坦性自体・一般B4は
未完成として保持する。既存共通完備化ディレクトリの検索では離散性や一般の導来Nakayama判定の
公開入口は確認できなかったため、次はこの差分を具体的BS対象と既存APIでどう埋めるか調べる。
共有・CLMST・利用先・共有監査は編集していない。

## 共通基盤への要求 G9：有界p冪ねじれ係数上のp完全平坦対象の離散性（要求受領確認済み・API未実装）

対象と正確な仮定：可換環T:Type u、素数p、X:DerivedCategory.Minus (ModuleCat T)。
hT : ∃ N:ℕ, ∀ n:ℕ, ∀ t:T, (p:T)^n*t=0 → (p:T)^N*t=0。
hX : DerivedCompletion.IsComplete T (p:T) X.obj。
q=Ideal.Quotient.mk (Ideal.span {(p:T)})、Y=(boundedAboveDerivedBaseChange q).obj Xとし、
∀ i:ℤ, i≠0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat (T/(p))) i).obj Y.obj)、
Module.Flat (T/(p)) ((DerivedCategory.homologyFunctor (ModuleCat (T/(p))) 0).obj Y.obj)を仮定する。
求める結論：X.obj.IsGE 0かつX.obj.IsLE 0、およびH=(DerivedCategory.homologyFunctor (ModuleCat T) 0).obj X.objについて
∃ N:ℕ, ∀ n:ℕ, ∀ x:H, (p:T)^n • x=0 → (p:T)^N • x=0。
Noether性、有限生成性、Tのp正則性、古典的完備性は追加しない。

利用BS工程：著者公開版Lemma 3.7(2)の、具体的候補をA/(dⁿ)へ実導来基底変更して離散性を得る部分。
原典はここでBMS19 Lemma 4.7を参照しているが、本要求は新引用やsorryを加えるものではなく、
上記の具体的な共通導来加群補題の証明済みAPIを求める記録である。BSのprism・δ・環候補の接続はBSが担当する。
既存APIの不足：既存CompletelyFlatは加群のTor消滅、G3は既に離散な加群の主元判定を扱う。
共有DerivedCompletion・Mathlib導来圏の検索では上記の複体の離散性の入口を確認できなかった。
G7の逐次colimit交換、G8の係数制限交換とも異なる。
待つ工程：有界p冪ねじれを持つA/(dⁿ)上の実候補の離散性・有界ねじれを得る判定部分。
独立作業：既存perfect prismの有界ねじれ入力を再利用し、正則dの冪商の実Koszul比較、
元のAへ制限したp完備性、標準単位と剰余の比較を具体的対象について進める。
G9はユーザーの個別許可「G9を送ってよい」を受け、2026-10-15にCLMSTへ上記の仮定・結論と利用工程を送信した。送信成功を確認済み。CLMST正本の2026-10-15付G9受領記録も確認したが、同記録では未実装・未受渡しである。BS内で共通一般補題を重複定義しない。

### 次工程の登録：具体的候補の正則生成元冪商とp導来完備性

BS専用DeltaRootSourceGeneratorPowerReduction.leanを新設する。
正則dと任意nについて、具体的逐次対象をA/(dⁿ)へ実導来基底変更してAへ制限した対象を、
既存restrictedDerivedQuotientKoszulIsoでdⁿの実Koszul錐へ比較する。
具体的逐次対象のp導来完備性と既存の写像錐に関する閉性を使い、この実制限対象のp導来完備性を証明する。
n=0の単元商・零環も含め、p正則性・ghost・G7・d mod p正則性は要求しない。
原典Lemma 3.7の離散性をこの比較だけで結論せず、G9・G8待ちと独立に進める。
全公開宣言を専用監査し、共有・CLMST・共有監査は編集しない。

## B4-6：具体的逐次候補の生成元冪商とp導来完備性（2026-10-15）

DeltaRootSourceGeneratorPowerReduction.leanで、正則dの任意冪dⁿによる実導来還元を
元のAへ係数制限した対象と、同じ候補の実dⁿ Koszul錐との比較同型を公開した。
既存の正則主元商Koszul比較を再利用し、候補のp導来完備性と写像錐に関する閉性から、
この係数制限後の対象のp導来完備性も証明した。n=0の零商を含む。
p正則性・ghost単射・G7・d mod p正則性は今回の2宣言に不要である。
対象3806ジョブ成功（共有の既存警告のみ）、B4全体pure監査1983報告成功、標準3公理のみ。
新sorry・公理・引用なし。G9要求は許可に基づき送信し、CLMST正本の受領記録を確認した。
G9のAPIは未実装・未受渡し。商環上の完備性への係数環比較G8、離散性G9、
環H0候補との接続・完全忠実平坦性自体・一般B4は引き続き未完成として保持する。
共有・CLMST・利用先・共有監査は編集していない。

### 次工程の登録：生成元冪商における最後の完備化単位の比較

DeltaRootSourceGeneratorPowerReduction.leanを拡張する。
正則dの各冪商A/(dⁿ)への実基底変更について、最後のd完備化の標準単位が同型に移ることを、
既存CompletionQuotientの任意冪版から証明する。実p完備化対象の還元と逐次対象の還元を、
この標準単位の像そのもので比較し、その逆射との正確な両立式を公開する。
これにより各生成元冪商の段階で最後のd完備化を除ける。離散性やG8の係数環比較とは区別する。
既存一般完備化APIを再利用し、新規一般補題・共有層の変更は行わない。
さらに、この単位による比較と前工程の実Koszul比較が可換となる図式を、既存Koszul比較の自然性から公開する。

## B4-6：生成元冪商で最後のd完備化を除く標準比較（2026-10-15）

DeltaRootSourceGeneratorPowerReduction.leanに4公開宣言を追加した。
具体的な実p完備化済み源から逐次p,d完備化候補への標準d完備化単位が、
任意のA/(dⁿ)への実導来基底変更で同型になることを既存の任意冪商定理から証明した。
この単位の像そのもので各段階の比較同型を定め、逆射との両立式を公開した。
さらに、Aへ係数制限したこの比較が、前工程の実Koszul比較の下で
標準単位のdⁿ錐上の射と一致する図式を、既存比較の自然性から証明した。
n=0を含み、今回もd正則性のみでp正則性・ghost単射・G7は要求しない。
対象3806ジョブ成功（共有の既存警告のみ）、B4全体pure監査1987報告成功、標準3公理のみ。
新sorry・公理・引用なし。自分の検証済みBS専用変更のみを個別コミットする。
これらは各冪商での最後の完備化の除去であり、商環上の完備性G8や離散性G9を解消していない。
原典Lemma 3.7にG9を適用する際は、A/(dⁿ,p)での実還元の次数零集中・平坦性も必要である。
既証のA/(d,p)での結果だけで任意nの場合を結論せず、冪零厚化に沿う実導来平坦性の議論を別途確認する。
一般B4・環H0候補との接続・完全忠実平坦性自体は未完成として保持する。

### 次工程の登録：根添加候補へのprism基底射と既存商射との接続

BS専用DeltaRootPrismBaseMap.leanを新設する。
DeltaRootPerfectoidCandidateの既存raw射と多項式係数包含の合成を、prism台環への係数射として明示する。
標準δ射の合成であること、dを候補の選択生成元そのものへ送ること、主イデアル像の一致を証明する。
元のoriented prismの生成元がdistinguishedなら、この射を既存OrientedPrism.Homへ束ねる。
誘導商射が既存deltaRootPerfectoidCandidateBaseMapに一致することを、商代表上の図式で証明する。
新しい候補・prism・perfectoid性の定義は作らず、完全忠実平坦性や離散性をこの射の存在から結論しない。
全公開宣言をBS専用監査し、共有層・CLMST・利用先は編集しない。

## 共通基盤への要求 G10：冪零イデアルに沿う実導来平坦性の持ち上げ（要求受領確認済み・API未実装）

対象と正確な仮定：可換環T:Type u、I:Ideal T、hI:∃N:ℕ,I^N=⊥、
X:DerivedCategory.Minus (ModuleCat T)。q=Ideal.Quotient.mk I、
Y=(boundedAboveDerivedBaseChange q).obj Xとする。
∀i:ℤ,i≠0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat (T⧸I)) i).obj Y.obj)、
Module.Flat (T⧸I) ((DerivedCategory.homologyFunctor (ModuleCat (T⧸I)) 0).obj Y.obj)を仮定する。
求める結論：X.obj.IsGE 0かつX.obj.IsLE 0、および
Module.Flat T ((DerivedCategory.homologyFunctor (ModuleCat T) 0).obj X.obj)。
Noether性、有限生成性、正則性は要求しない。n=0のI=⊤・零環の枝もhIを満たす範囲で含む。

利用BS工程：著者版Lemma 3.7(2)で、実A/(dⁿ)還元がp完全平坦であることの具体的入力。
n>0についてT=A/(dⁿ,p)、Iはdの像の主イデアルとし、Iⁿ=0とT/I≃A/(p,d)の
具体的な環同型・実二段基底変更比較はBSで供給する。既証の実A/(p,d)還元が次数零・平坦なので、
本判定を使って実A/(dⁿ,p)還元も次数零・平坦とし、G9の仮定へ渡す。
n=0はA/(1)=0としてBSで別処理する。
既存APIの不足：共通導来完備化・導来圏・平坦性の検索では、任意の上有界実対象に対する
この冪零厚化の離散性・平坦性判定の公開入口を確認できなかった。
G3は既に離散な加群、G9はp完備対象に対する有界pねじれ係数上の判定であり、本要求とは異なる。
待つ工程：任意nの実A/(dⁿ,p)還元への平坦性の移送だけ。
独立作業：prism基底射・既存商射との接続、具体的な二段商と冪零イデアルの型・標準写像の比較。
G10はユーザーの個別許可「G10を送ってよい」を受け、2026-10-15に上記の仮定・結論と利用工程をCLMSTへ送信した。送信成功を確認済み。APIは未受領であり、BS内で共通一般判定を重複定義しない。

## B4-6：根添加prism候補への基底射と既存perfectoid商射（2026-10-15）

DeltaRootPrismBaseMap.leanに6公開宣言を実装した。既存raw射と多項式係数包含の合成を
prism台環への具体的係数射として公開し、δ両立・選択生成元の厳密な保存・主イデアル像の一致を証明した。
生成元がdistinguishedな元のoriented prismから既存候補へのOrientedPrism.Homを構成し、
その誘導商射が既存deltaRootPerfectoidCandidateBaseMapと一致することを商代表上で証明した。
任意の元族を扱い、Unique σやp正則性・G7・G8・G9は今回の宣言には仮定しない。
完全prismの場合のdistinguished性は既存isDistinguished_of_perfectから供給できる。
対象3768ジョブ成功（警告なし）、B4全体pure監査1993報告成功、標準3公理のみ。
新sorry・公理・引用なし。候補への射を具体化した成果であり、CFFや一般B4を証明済みとは扱わない。
G10はユーザーの個別許可を受けてCLMSTへ正確な仮定・結論と利用工程を送信し、送信成功を確認した。
具体的な冪零商・二段商の比較は引き続きBSの独立作業とし、共有・CLMST・利用先は編集していない。

### 次工程の登録：prism係数の冪剰余における具体的冪零商

BS専用PrismaticPowerResidueNilpotent.leanを新設する。
可換環Aとa,d:AについてTₙ=A/(a,dⁿ)、Kₙ=(dの像)を明示し、Kₙⁿ=0を証明する。
n>0ならA/(a,dⁿ)→A/(a,d)の標準全射、核Kₙ、その誘導商同型と標準商射の両立を公開する。
a=pの場合がG10への具体的入力である。正則性・Noether性・p素数性はこの環計算に不要。
n=0ではT₀=0であり、一般のA/(a,d)への射を作らない。冪零性自体はn=0も含む。
既存Mathlibの商・核・商核同型を再利用し、新しい一般的導来判定は定義しない。
全公開宣言をBS専用監査し、共有・CLMST・利用先は編集しない。

### 次工程の登録：冪零厚化を経由する実二段基底変更

BS専用PrismaticPowerResidueDerived.leanを新設する。
正のnについて、A→Tₙ=A/(a,dⁿ)→A/(a,d)の具体的標準全射の合成に沿い、
実A/(a,d)基底変更と、Tₙへの実基底変更の後に実冪零剰余射を適用した対象との比較同型を構成する。
通常係数拡大の標準合成同型を選択射影モデルへ適用し、既存の実基底変更モデル比較で降ろす。
G10の次数零・平坦性判定自体は実装せず、既証のA/(a,d)還元をG10の経路へ接続する具体的導来同型に限る。
新規一般導来関手を定義せず、共有・CLMST・利用先は編集しない。

## B4-6：生成元冪剰余の具体的な冪零厚化（2026-10-15）

PrismaticPowerResidueNilpotent.leanに10公開宣言を実装した。
Tₙ=A/(a,dⁿ)内のKₙ=(dの像)についてKₙⁿ=0をn=0も含め証明した。
n>0では標準環射Tₙ→A/(a,d)を構成し、全射性・核Kₙ・(Tₙ/Kₙ)≃A/(a,d)を
具体的な標準商射の合成との両立付きで証明した。任意a,dを扱い、a=pが利用する場合である。
正則性・Noether性・素数性を仮定せず、n=0に非零環への射を作る誤った一般化は行わない。
対象2490ジョブ成功（警告なし）、B4全体pure監査2003報告成功、標準3公理のみ。
新sorry・公理・引用なし。CLMST正本のG10受領記録を確認したが、同記録は未実装・未受渡しである。
この環計算だけで実冪剰余の平坦性や離散性を結論せず、実二段比較とG10/G9を別工程として保持する。
自分の検証済みBS専用変更のみを個別コミットする。共有・CLMST・利用先は編集していない。

## B4-6：冪剰余と冪零剰余射を経由する実二段基底変更（2026-10-15）

PrismaticPowerResidueDerived.leanに2公開同型を実装した。A→Tₙ=A/(a,dⁿ)→A/(a,d)の
具体的標準射の合成式を使い、Mathlibの通常係数拡大の合成同型を複体へ持ち上げた。
選択射影モデルと既存の実基底変更モデル比較を合成して、実A/(a,d)基底変更と
Tₙへの実基底変更の後に実冪零剰余射を施した対象との同型を証明した。
n>0だけを仮定し、正則性・平坦性・完備性はこの同型には不要。
対象2491ジョブ成功（警告なし）、B4全体pure監査2005報告成功、標準3公理のみ。
新sorry・公理・引用なし。これにより既証の一乗剰余計算を二段階の実対象へ移せる。
G10自体、任意nの冪剰余対象の離散性・平坦性、G8/G9、環候補との接続・CFF・一般B4は別工程である。
共有・CLMST・利用先は編集していない。

### 次工程の登録：具体的逐次根添加対象の冪零還元への既証計算の移送

BS専用DeltaRootSourcePowerResidue.leanを新設する。
具体的逐次p,d完備化対象Xを実A/(p,dⁿ)還元してから、標準冪零剰余射で実還元した対象について、
前工程の二段比較を使い、既証の実A/(p,d)還元のraw single比較・非零次数消滅・H0忠実平坦性を移す。
n>0、p正則性・d正則性・自由δ源ghost単射・指定単元δd・既存G7交換入力を明示して保持する。
A/(p,dⁿ)上の元の対象の離散性・平坦性は結論しない。そこはG10を適用する次工程である。
既存環候補との同一視やCFF自体を追加せず、全公開宣言を専用監査する。

## B4-6：具体的根添加対象の実冪零還元のsingle比較とH0忠実平坦性（2026-10-15）

DeltaRootSourcePowerResidue.leanに3公開宣言を実装した。具体的逐次p,d完備化対象Xについて、
実A/(p,dⁿ)還元の後に標準冪零剰余射で実還元した対象を、前工程の比較の逆を使って
既存の実A/(p,d)還元へ戻し、標準係数作用付きraw商のsingle比較を公開した。
この二段実還元の非零次数ホモロジー消滅と、A/(p,d)上のH0忠実平坦性も証明した。
n>0、元のp正則性・d正則性・自由δ源ghost単射・指定単元δd・具体的G7交換入力を保持する。
対象3807ジョブ成功（共有の既存警告のみ）、B4全体pure監査2008報告成功、標準3公理のみ。
新sorry・公理・引用なし。今回の仮定はG7の具体的関手がcolimitを保つという入力であり、
G7の一般APIやその入力供給を解消したとは扱わない。G10は要求受領確認済み・API未受領。
二段還元の平坦性と、A/(p,dⁿ)上の中間対象自体の平坦性・離散性は区別する。
後者へのG10、商環上の完備性G8、有界ねじれと離散性G9、環候補への接続・CFF・一般B4は未完成。
自分の検証済みBS専用変更のみを個別コミットする。共有・CLMST・利用先は編集していない。

### 次工程の登録：G10の標準冪零商射に合わせた実還元比較

BS専用PrismaticPowerResidueCanonical.leanを新設する。
Tₙ=A/(a,dⁿ)、Kₙ=(dの像)、e:Tₙ/Kₙ≃A/(a,d)を前工程の具体的同型とする。
標準射r:Tₙ→A/(a,d)についてe⁻¹∘r=q_Kを証明し、通常係数拡大の合成と
既存restrictScalarsIsoExtendInverseから、extend q_K≅extend r⋙restrict eを構成する。
この比較を複体と実導来基底変更へ持ち上げ、G10が要求する実q_K還元を、
既証の実r還元のeによる係数制限と比較する。新しい係数変更・離散性判定は定義しない。
共通G10の実装を待たずに入力型を一致させる作業であり、全宣言をBS専用監査する。

## B4-6：G10の標準冪零商射との実導来比較（2026-10-15）

PrismaticPowerResidueCanonical.leanに4公開宣言を実装した。Tₙ=A/(a,dⁿ)、Kₙ=(dの像)、
既存e:Tₙ/Kₙ≃A/(a,d)についてe⁻¹∘r=q_Kを証明した。Mathlibの係数拡大の合成と
既存restrictScalarsIsoExtendInverseを使ってextend q_K≅extend r⋙restrict eを構成し、
複体・既存の実導来基底変更へ持ち上げた。G10の標準商射による還元を、
既証のrによる実還元をeで係数制限した対象に比較できる。
対象2825ジョブ成功（警告なし）、B4全体pure監査2012報告成功、標準3公理のみ。
新sorry・公理・引用なし。新しい係数変更概念・一般的離散性判定を定義せず、
正のn以外に正則性・平坦性・完備性はこの比較には仮定しない。
次は具体的根添加対象のr還元の既証計算をこの標準q_K還元へ移す。
G10・G8・G9自体、環候補との接続・CFF・一般B4は未完成として保持する。

### 次工程の登録：具体的根添加対象のG10標準還元入力

BS専用DeltaRootSourceCanonicalPowerResidue.leanを新設する。
既存の実A/(p,dⁿ)還元YとKₙ=(dの像)について、標準商射q_Kによる実還元のraw single比較、
非零次数消滅、H0の(A/(p,dⁿ))/Kₙ上の忠実平坦性を証明する。
前工程の標準商比較・既存の実r還元計算・正確な係数制限を使い、商同型を介する
忠実平坦性は既存Module.FaithfullyFlat.transと線形同値から供給する。
G7の具体的交換・p,d正則性・ghost単射等の入力は保持し、G10そのものやYの離散性は結論しない。
全公開宣言をBS専用監査し、共有・CLMST・利用先は編集しない。

## B4-6：具体的根添加対象のG10標準還元入力（2026-10-15）

DeltaRootSourceCanonicalPowerResidue.leanに3公開宣言を実装した。
具体的逐次対象Xの実Tₙ=A/(p,dⁿ)還元Yについて、G10の標準商射Tₙ→Tₙ/Kₙによる実還元を
前工程の比較で既証のr還元の係数制限に戻し、正確な商環上のraw single比較を構成した。
非零次数ホモロジー消滅も証明し、H0忠実平坦性は商同型eから得るTk-代数同型、
既存Module.FaithfullyFlat.trans、ホモロジーと係数制限の既存比較を合成して証明した。
これによりKₙⁿ=0と併せ、G10が受け取る実標準商還元の次数零集中・H0平坦性の入力を
具体的な既存実対象について供給できた。G10の結論自体は仮定も新定義もしていない。
n>0、p正則性・d正則性・自由δ源ghost単射・指定単元δd・G7の具体的交換入力を保持する。
対象3809ジョブ成功（共有の既存警告のみ）、B4全体pure監査2015報告成功、標準3公理のみ。
新sorry・公理・引用なし。G10の共通APIは正本上なお未実装・未受渡し。
G10によるY自体の離散性・平坦性、生成元冪商を先に取るG9のp還元との比較、G8/G9、
環候補との接続・CFF・一般B4は未完成として保持する。共有・CLMST・利用先は編集していない。

### 次工程の登録：生成元冪商を先に取るG9の標準mod p還元

BS専用PrismaticGeneratorPowerModP.leanを新設する。
T=A/(dⁿ)、Q=A/(p,dⁿ)について標準全射r:T→Q、核(p:T)、e:T/(p)≃Qを
具体的な標準商射との両立付きで構成する。n=0の零商も含み、正則性・素数性は要求しない。
次に、XのTへの実基底変更を標準mod p商射で実還元した対象を、
実Q還元のeによる係数制限へ比較する。Mathlibの係数拡大の合成、
既存の商同型による係数制限比較、選択射影モデルと既存実基底変更モデル比較を再利用する。
これによりG9のmod p入力とG10側のQ還元を正確な実対象・係数環で接続する。
離散性・平坦性・G8/G9/G10自体は別工程。全公開宣言を専用監査し、共有層は編集しない。
同じモジュールで、この実比較と既存の係数制限・ホモロジー比較を合成し、全次数ホモロジー同型、非零次数消滅の移送、H0平坦性の移送も証明する。平坦性そのものはQ還元側の明示入力として保持する。

## B4-6：G9の生成元冪商上の標準mod p還元と二生成剰余の接続（2026-10-15）

PrismaticGeneratorPowerModP.leanに12公開宣言を実装した。
T=A/(dⁿ)からQ=A/(p,dⁿ)への具体的標準全射を構成し、その核が(p:T)であること、
e:T/(p)≃Qと両方向の標準商射の合成式を証明した。
Mathlibの係数拡大の合成と既存restrictScalarsIsoExtendInverseを複体上で合成し、
実T還元の後に標準mod p射で実還元した対象を、実Q還元をeで係数制限した対象へ比較した。
全次数ホモロジー同型、次数消滅の移送、Q上のH0平坦性をT/(p)上のH0平坦性へ移す補題も公開した。
最後の平坦性はQ側の明示的な入力であり、G10の結論を供給済みとは扱わない。
全宣言は任意nで成立し、n=0の零商を含む。素数性・正則性・完備性をこの比較に追加していない。
対象2826ジョブ成功（警告なし）、B4全体pure監査2027報告成功、標準3公理のみ。
新sorry・公理・引用なし。G10の入力が標準商環上で供給済みである前工程と、
G10の出力となるQ上の次数零集中・H0平坦性をG9の標準mod p入力へ渡す今回の比較を区別する。
G10/G8/G9の共通APIは未受領、G7交換・ghost入力の供給、環候補との接続・CFF・一般B4も未完成。
自分の検証済みBS専用変更のみを個別コミットする。共有・CLMST・利用先は編集していない。

## 共通G4・G6の供給確認と再開（2026-10-15）

CLMST正本のG4・G6実装記録と実ソースを確認した。
G4はCommutativeAlgebra/WittGhostInjective.leanの
witt_ghostMap_injective_of_mul_prime_injective p A hpであり、p乗算単射以外の追加仮定はない。
G6はDerivedCompletion/Jacobson.leanのmem_jacobson_bot_of_isModuleComplete R a hであり、
古典的完備性・p正則性・有界ねじれを要求しない。
G7〜G10やG3の受渡し完了とは区別し、受領済みの2APIだけをBSへ接続する。
ユーザー指定に従い、他チャットへの追加送信は行わない。

### 次工程の登録：実導来p除算候補の具体的な単元係数

BS専用DeltaPDivisionDerivedUnit.leanを新設する。
既存DerivedDeltaDivisionCompletion D p aにおける除算変数の標準像を明示し、
pとの積が指定元a_sの像に一致することを証明する。既存derivedDeltaDivision_complete_pをG6へ適用し、
この実候補でpがJacobson根基に属することを証明する。
a_sがdistinguishedなら、既存δ射とisDistinguished_factorから標準変数像の単元性、
a_s=p*uという具体的単元係数を得る。古典的完備化への置換・p正則性の追加はしない。
全公開宣言をBS専用監査し、検証済みの自分の変更だけを個別コミットする。

### 次工程の登録：G4による具体的根添加源のghost単射入力供給

BS専用DeltaRootSourceRegularGhost.leanを新設する。
元の係数環Aのp正則性から、多項式環Pと自由δ源Lのp正則性を既存平坦性で供給し、
共通G4を適用して実際のL上のWitt ghostMap単射を証明する。
この入力を具体的逐次根添加対象のG10標準冪零還元の次数消滅・H0忠実平坦性に渡し、
追加のghost単射仮定なしの公開入口を構成する。G7の具体的colimit交換入力は保持する。
新しいWitt一般定理を作らず、元のperfectoid環にp正則性を追加する最終定理には変更しない。
全公開宣言を専用監査し、検証済みのBS専用変更のみを個別コミットする。

## B4-6：G6を用いた実導来p除算候補の単元係数（2026-10-15）

DeltaPDivisionDerivedUnit.leanに5公開宣言を実装した。
既存の実H0候補における標準除算変数の像とp*u_s=j(a_s)の関係式を公開した。
既存derivedDeltaDivision_complete_pと共通G6を合成し、この実候補でpがJacobson根基に属することを証明した。
指定元a_sがdistinguishedなら、既存のδ射・isDistinguished_factorからu_sが単元であること、
標準変数像そのものを単元係数とするa_s=p*u_sの存在を証明した。
任意σ・任意δ環を許し、p正則性・有界ねじれ・古典的完備性は仮定しない。
実導来候補を古典的完備化へ置き換えず、G6が待合せだったこの単元性工程を解消した。
対象2886ジョブ成功（警告なし）、B4全体pure監査2032報告成功、標準3公理のみ。
新sorry・公理・引用なし。G3・G7〜G10、環候補との接続・CFF・一般B4は未完成として保持する。
共有・CLMST・利用先は編集せず、他チャットへの追加送信も行っていない。

## B4-6：G4による実自由δ源のghost単射供給（2026-10-15）

DeltaRootSourceRegularGhost.leanに3公開定理を実装した。
Aのp正則性を多項式環P=MvPolynomial σ Aと実自由δ源Lへ既存の平坦性で移し、
共通G4を適用してWittVector p Lの実ghostMapの単射性を証明した。
この証明済み入力をG10標準冪零還元の既存2定理へ適用し、独立のghost単射仮定なしで
非零次数ホモロジー消滅とH0忠実平坦性を供給する公開入口を追加した。
G7の具体的PreservesColimit入力、d正則性・指定単元δd・n>0・Unique σはこの2入口に保持する。
元のperfectoid環R自体のp正則性を最終B4の入力に追加する変更はしていない。
対象3811ジョブ成功（共有の既存警告のみ）、B4全体pure監査2035報告成功、標準3公理のみ。
新sorry・公理・引用なし。G4とG6の供給により独立に進められる証明を再開し、
実候補の単元性と自由δ源ghost入力の待合せを解消できた。
G3・G7〜G10、環候補との接続・CFF・一般B4は引き続き未完成として保持する。
他作業を上書き・ステージせず、自分の検証済みBS専用変更のみを個別コミットする。
他チャットへの追加送信は行っていない。

## G7・G8・G3のBS接続実行計画（2026-10-16）

ユーザー指定「この三つを完成させてください」に従い、以下の3単位を順に実装・監査・個別コミットする。
共通側のTorSequentialColimits、RestrictionCompletion、CompletelyFlatCriterionの証明済みAPIを再利用する。

1. DeltaRootSourceSequentialTor.lean：G7を具体的有限源図式と標準剰余射へ適用し、
   G10標準還元の非零次数消滅・H0忠実平坦性の公開入口からPreservesColimit入力を除く。
   G4で供給済みのghost単射を使い、外部Tor交換仮定・ghost仮定のない結果にする。
2. DeltaRootSourceGeneratorPowerComplete.lean：G8の元の完備化単位を保つ自然同型と
   係数制限の同型反映を使い、既証のAへ制限したp完備性を、A/(dⁿ)上のp導来完備性へ移す。
   BSの具体的還元対象を扱い、新しい一般係数制限・完備性定義は作らない。
3. FreeDeltaFrobeniusCompletelyFlat.lean：自由整数δ環の実Frobeniusで作用する加群を明示し、
   p正則性と既証mod p忠実平坦性を、正確な商テンソルの係数作用を保ってG3へ渡す。
   混標数Frobeniusの既存IsCompletelyFaithfullyFlatを証明する。

新sorry・公理・引用は追加しない。全公開宣言をBS専用監査へ登録し、対象ビルドとpure監査後に
各単位の検証済みBS専用変更だけをコミットする。共有・CLMST・利用先は編集せず、追加送信も行わない。
この3接続の完成と、G9・G10および一般B4全体の完成を区別する。

## G7のBS接続完了（2026-10-16）

DeltaRootSourceSequentialTor.leanに3公開定理を実装した。
具体的な有限評価源図式Fと実剰余射ψについて、G7から各正次数のPreservesColimitを供給した。
既存G4接続と合成し、G10標準冪零還元の非零次数消滅・H0忠実平坦性を、
外部colimit交換入力・ghost単射入力なしで証明した。既存の仮定付き入口は互換のため保持する。
p正則性・d正則性・指定単元δd・Unique σ・n>0は従来の具体的幾何入力として明示している。
対象3859ジョブ成功（共有の既存警告のみ）、pure B4監査2038報告成功、標準3公理のみ。
新sorry・公理・引用なし。G7の一般APIの再実装はせず、実際の有限源Torから全源への移送に適用した。
これはG10の入力を引用なしで供給する成果であり、G10自体や一般B4の完成とは区別する。

## G8のBS接続完了（2026-10-16）

DeltaRootSourceGeneratorPowerComplete.leanで、正則dの各冪商T=A/(dⁿ)への実還元Yが、
T自身の係数作用についてp導来完備であることを証明した。
既証のAへ制限したp完備性から、G8の元の標準完備化単位の図式を使い、
T上の標準単位を係数制限した射が同型であることを示した。
既存derivedRestrictScalarsの同型反映でT上の単位の同型性を得て、既存の完備性判定へ戻した。
n=0を含み、p正則性・ghost・Tor交換・古典的完備性・有界ねじれを追加していない。
対象3816ジョブ成功（共有の既存警告のみ）、pure B4監査2039報告成功、標準3公理のみ。
新sorry・公理・引用なし。G9が必要とする商環上の実p完備性の入力を供給できた。
新しい一般係数制限補題をBS内に作らず、共通G8の自然同型・単位図式をそのまま再利用した。
G9・G10と一般B4全体は未完成として保持する。

## G3のBS接続完了（2026-10-16）

FreeDeltaFrobeniusCompletelyFlat.leanに12公開宣言を実装した。
自由整数δ環Aの実Frobeniusφで作用する終域B=ULift Aを、pを持つ明示的な型とAlgebra構造で区別した。
(algebraMap A B x).down=φ(x)を公開し、この作用が元の実Frobeniusそのものであることを確認した。
p主イデアルの拡大の一致、Bの実p剰余と既存mod p Frobenius終域との標準像を保つ環同型、
その正確なA/p線形性を証明した。G3の通常商テンソル(A/p)⊗_A Bを既存の忠実平坦な
mod p Frobenius加群へ線形同値で比較し、通常剰余テンソルの忠実平坦性を証明した。
pがAとφ作用を持つBの双方で正則であることを供給し、共通G3をそのまま適用して
freeDeltaFrobenius_isCompletelyFaithfullyFlatを証明した。
任意σを許し、Noether性・有限生成性・完備性は追加していない。自由整数δ環上の結果であり、
元の任意perfectoid環自体のp正則性を仮定する変更はしていない。
対象3567ジョブ成功（警告なし）、G7・G8接続も含むpure B4監査2051報告成功、標準3公理のみ。
新sorry・公理・引用なし。共通層を編集せず、BS専用の具体的な環・作用・通常商比較に適用した。

今回指定された3接続は完了：G7の具体的colimit交換入力供給、G8の商環上のp実導来完備性、
G3の自由δ Frobeniusのp完全忠実平坦性。各段階で対象ビルド・pure監査を行い個別コミットする。
これらと、冪剰余対象の離散性・環H0候補との接続・一般根付きCFF拡大・一般B4全射性の完成は区別する。
既存André引用・B-I/B6引用を使わず、削除・弱化もしていない。他チャットへの追加送信は行っていない。

## G10受領後のBS接続計画（2026-10-16）

DeltaRootSourcePowerResidueDiscrete.leanをBS担当で新設する。
共通derived_pure_flat_of_nilpotent_reductionを、具体的T=A/(p,dⁿ)、
K=(dの像)、実逐次PD完備源のTへの実導来還元へ適用する。
G4・G7接続の既証入力とK^n=0を渡し、元のT還元の離散性とH0平坦性を証明する。
続いてDeltaRootSourceGeneratorPowerModPFlat.leanを新設し、既存の標準商比較で
A/(dⁿ)上の標準mod p還元に次数消滅・平坦性を渡す。
G8による商上p完備性と合わせてG9への入力を揃える。現時点で共通正本はG9未完成と記録しており、
G9の一般判定をBSで重複実装しない。各段階をビルド・専用監査後に個別コミットする。

## G10のBS実対象への適用完了（2026-10-16）

DeltaRootSourcePowerResidueDiscrete.leanに3公開定理を実装した。
実T=A/(p,dⁿ)還元Yに対し、K=(dの像)の冪零性とG4・G7で供給した
標準K還元の純性・H0忠実平坦性を、共通G10へ直接渡した。
YのIsGE 0・IsLE 0・H0平坦性、全非零次数ホモロジー消滅を証明した。
n>0、Unique σ、Aのp正則性、d正則性、指定単元δdを正確に保持している。
対象3883ジョブ成功（共有の既存警告のみ）、pure B4監査2054報告成功、標準3公理のみ。
新sorry・公理・引用なし。G10側の入力だけの成果から、実冪剰余自体の離散・平坦性へ進んだ。
G9・環候補との接続・一般CFF根拡大・一般B4は未完成として保持する。

## G9標準mod p入力のBS接続完了（2026-10-16）

DeltaRootSourceGeneratorPowerModPFlat.leanに3公開定理を実装した。
G10で得たA/(p,dⁿ)への実還元の次数消滅・H0平坦性を、既存の
prismaticGeneratorPowerModP比較でT=A/(dⁿ)上の標準mod p実還元へ移した。
さらにG8による実T対象のT上p導来完備性と合わせ、
deltaRootSourceGeneratorPower_G9_inputsで3条件を具体的対象のまま公開した。
共通G9はFlatPowerTorsionの逆極限ねじれ評価までは完成したが、
元の実導来対象の離散性を結論する一般APIは未完成（共通正本G9-1）。
そのためG9自体の適用と実T対象H0の有界ねじれは未実装として区別する。
係数環Tの有界ねじれは完全δ環の場合の既証
IsPerfect.distinguished_quotient_power_p_pow_torsion_killed_by_p_powを再利用する予定で、
同等の一般ねじれ定義・補題を重複作成していない。
対象3897ジョブ成功（共有の既存警告のみ）、pure B4監査2057報告成功、標準3公理のみ。
新sorry・公理・引用なし。2段階を個別コミットし、共有・CLMST・利用先は編集していない。
一般B4全射性・候補環との接続・一般CFF根拡大は引き続き未完成。他チャットへ送信していない。

## G9待合せ中の忠実性持ち上げ計画（2026-10-16）

BS担当でDeltaRootSourcePowerResidueFaithful.leanを新設する。
G10で離散・平坦と判明した実A/(p,dⁿ)還元を、その実H0の単一対象と比較する。
共通の実導来基底変更H0比較を再利用して、標準冪零剰余の実H0と
元の実H0の通常剰余テンソルを同型で結ぶ。既証剰余忠実平坦性を移し、
共通の有限冪ねじれ加群の零性検出を、d^n=0の具体的係数環に適用して
元の実H0自体の忠実平坦性を証明する。一般冪零判定はBSに重複実装しない。
G9の一般離散性判定を待つ工程とは独立であり、対象ビルド・専用監査後に個別コミットする。

## 実冪剰余H0の忠実平坦性への強化（2026-10-16）

DeltaRootSourcePowerResidueFaithful.leanに4公開宣言を実装した。
G10で得た実T=A/(p,dⁿ)還元Yの離散性から、実H0を次数零に置く正規化同型を構成した。
これを標準K=(dの像)商の実基底変更へ送り、既存の自然H0比較により
実K還元のH0と通常の係数拡大(T/K)⊗_T H0(Y)を比較した。
既証の実剰余H0忠実平坦性を通常テンソルへ移し、共通の有限冪ねじれ零性検出を
T内のd^n=0へ適用して、実H0(Y)自体のT上通常忠実平坦性を証明した。
この工程はG9不要。従来のn>0・Unique σ・Aのp正則性・d正則性・単元δdは保持する。
一般冪零・平坦性判定は共通APIを再利用し、BS内に重複作成していない。
対象3886ジョブ成功（自分のモジュール警告なし、共有既存警告のみ）、
pure B4監査2061報告成功、標準3公理のみ、新sorry・公理・引用なし。
共通正本ではG9-3の実Koszul塔と通常冪余核塔の比較まで進んでいるが、
元の実対象の離散性・H0評価へ合流する一般G9はなお未完成。
本成果と生成元冪商の離散性・候補環のCFF・一般B4全射性の完成は区別する。

## 標準mod p還元への忠実性移送計画（2026-10-16）

既存BS専用DeltaRootSourceGeneratorPowerModPFlat.leanへ、実A/(p,dⁿ)還元H0の
忠実平坦性を、正確な標準商(A/(dⁿ))/p上の実mod p還元H0へ移す公開定理を追加する。
既存の商環同型・ホモロジー比較とMathlibの忠実平坦性の推移性を使い、
係数作用を明示する。さらに実mod p還元とその実H0の単一対象の同型を公開し、
後の通常剰余テンソル比較へ利用する。G9一般判定は重複実装しない。
対象ビルドと全BS依存監査後に、このBS専用の変更だけを個別コミットする。

## 標準mod p実還元の忠実平坦性（2026-10-16）

DeltaRootSourceGeneratorPowerModPFlat.leanに2公開宣言を追加した。
実A/(p,dⁿ)還元H0の忠実平坦性を、既存の具体的商環同型とH0比較に沿って
(A/(dⁿ))/p上へ移した。環同型のAlgebra作用、係数制限、作用の塔を明示し、
Mathlibの忠実平坦性の推移性と線形同値による移送を使用した。
さらに標準mod p実還元とその実H0の次数零対象の正規化同型を公開した。
G9不要、n>0・Unique σ・p正則性・d正則性・単元δdは保持する。
対象3900ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2063報告成功。
標準3公理のみ、新sorry・公理・引用なし。G9一般判定・候補環との接続・一般CFF根拡大・B4全体は未完成。

## 任意根族のG4入力供給計画（2026-10-16）

BS担当でDeltaRootFamilyRegularGhost.leanを新設する。
既存の任意根族p除算包の有限源および次の単根源のp正則性から、
共通Witt ghost単射G4を供給する。次の段の根添字にはPUnitを選び、
元の根族σは任意のまま保つ。既存のraw p正則性・実p完備化後のmod p
非零次数消滅・H0忠実平坦性の入口から、外部ghost仮定を除く。
新しいWitt一般APIは作らず、有限段の元の係数作用を使う。
p正則性と指定単元δpは明示し、任意perfectoid環自体のp正則性を最終B4へ追加しない。
対象ビルド・専用監査後にBS専用変更だけを個別コミットする。

## 任意根族のG4入力供給完了（2026-10-16）

DeltaRootFamilyRegularGhost.leanに3公開定理を実装した。
任意根族σの各有限部分集合に対する実自由δ源のp正則性を平坦性から得て、共通G4へ渡した。
次段のraw包のp正則性を受け取る自由δ源にもG4を適用し、補助添字PUnitを選択した。
これにより既存の任意根族raw p除算包のp正則性、元のA上の実p完備化後の標準mod p
実還元の全非零次数消滅とH0忠実平坦性を、外部ghost仮定なしで公開した。
σ自体のUnique・有限性は要求せず、p正則性と指定単元δpは保持する。
次段のghostはその段のp正則性から得ており、p正則性の証明への循環は作っていない。
対象3852ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2066報告成功。
標準3公理のみ、新sorry・公理・引用なし。共通・CLMST・利用先は編集せず追加送信も行っていない。
共通G9は最新記録G9-4まで進行したが、最終離散性と実H0への有界ねじれ評価は未完成。
今回の任意根族の入力解消は、それを待たず独立に完了した。環候補のCFF・一般B4は未完成。

## 任意根族raw包のG3適用計画（2026-10-16）

BS担当でDeltaRootFamilyRawCompletelyFlat.leanを新設する。
既存deltaRootRawCoefficientAlgebraの実A作用を用い、標準剰余テンソル
(A/p)⊗_A Bを既存の通常係数拡大と同型で結び、既証raw実p商との標準線形比較に接続する。
G4接続からghost単射を供給し、通常剰余テンソルの忠実平坦性を証明する。
Aのp正則性と任意根族raw包のp正則性を正確なAスカラー作用に直して共通G3へ渡し、
元のA→Bがp完全忠実平坦であることを証明する。
Aのp正則性と指定単元δpは明示し、任意perfectoid環上の最終B4への仮定追加はしない。
既存の商・テンソル・完全平坦性定義を再利用し、新sorry・引用なしでビルド・監査・個別コミットする。

## 任意根族raw p除算包のp完全忠実平坦性（2026-10-16）

DeltaRootFamilyRawCompletelyFlat.leanに3公開定理を実装した。
元のA作用は既存deltaRootRawCoefficientAlgebraを使用し、その実係数射の一致は
既存deltaRootRawCoefficientAlgebra_algebraMapで保証される。
通常の剰余テンソル(A/p)⊗_A Bは、既存deltaRootRawBaseChangeModPAlgEquivで
標準A/p作用を持つ実raw p商へ直接比較できたため、同等の比較同型を新設しなかった。
G4でghost入力を供給した既存raw p商の忠実平坦性をこの比較で移し、
任意根族raw包のp正則性を正確なAのpスカラーについて示した。
共通G3へ両環のp正則性と通常剰余テンソル忠実平坦性を渡し、
deltaRootFamilyRaw_isCompletelyFaithfullyFlatを証明した。
任意σを許し、p正則性と指定単元δpを明示する。Noether性・有限生成性・完備性は追加しない。
対象3859ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2069報告成功。
標準3公理のみ、新sorry・公理・引用なし。共有・CLMST・利用先は編集していない。
これは実Frobenius根関係のraw p除算包のCFFであり、完備化・完全化後のperfectoid候補のCFFや
任意perfectoid環に関する一般B4全射性まで完成したとはしない。G9最終APIは現在も未完成。

## 完全prismを入力とする任意根族raw入口の計画（2026-10-16）

BS担当でPerfectPrismRootRawFlat.leanを新設する。
完全oriented prism Pについて、既存APIから係数環のp正則性・古典的p完備性を供給し、
Jacobson根基判定とδ環のpのdistinguished性からδpの単元性を内部供給する。
任意元族bについてraw p除算包のp完全忠実平坦性を公開する。
その元の係数環上の実p完備化のp導来完備性、標準mod p実還元の全非零次数消滅と
H0忠実平坦性を同じ具体的対象について公開する。G9適用の係数環ねじれ入力はp正則性により指数0。
G9の一般判定そのものは共有担当の作業を待ち、BSに重複実装しない。
各公開入口は完全prismと元族のみを入力とし、ghostや指定単元の追加仮定を持たせない。
対象ビルド・BS全依存監査後に個別コミットする。

## 完全prismから任意根族raw包・実完備化への公開入口（2026-10-16）

PerfectPrismRootRawFlat.leanに3公開定理を実装した。
完全oriented prismの古典的p完備性からpのJacobson根基所属を供給し、既存δ環APIでδpの単元性を得た。
完全δ構造のp正則性と合わせ、任意元族bのraw p除算包のp完全忠実平坦性を、
外部p正則性・ghost・指定単元仮定なしで公開した。
同じ実raw包を元のA上で実導来p完備化した対象について、p導来完備性と、
標準mod p実還元の全非零次数消滅・H0忠実平坦性を公開した。
公開入口の数学的入力は完全prismと元族だけである（完備性単独の定理はhP不要）。
源のp正則性からG9の係数環有界ねじれ指数0を使えるが、G9の一般判定をBSに再実装しない。
対象3869ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2072報告成功。
標準3公理のみ、新sorry・公理・引用なし。共有・CLMST・利用先は編集せず追加送信もしていない。
実p完備化自体の離散性、完備化・完全化後の候補CFF、一般B4は未完成として保持する。

## 実raw包の完全化における係数図式の登録（2026-10-16）

BS担当でDeltaRootPerfectionStages.leanを新設する。
既存raw根族Bと既存DeltaPerfectionを再利用し、n段の係数作用をφ_B^n∘jとする。
段ごとの型をULift Bで区別し、係数射・Algebra構造・Frobenius遷移AlgHom・
余極限への実標準AlgHomを構成する。既存deltaPerfectionOf_iterateを使い、
実余極限への全段の係数射の一致と隣接遷移の可換性を証明する。
これは完全化後CFFの段階別平坦性を接続するための実図式であり、
単に通常のA作用のままFrobeniusをA線形とみなすことを避ける。
一般の余極限や完全平坦性の同等定義は作らず、G9の一般判定も重複実装しない。
全公開宣言を専用監査し、対象ビルド後に個別コミットする。

## 実raw根族のFrobenius完全化の係数図式（2026-10-16）

DeltaRootPerfectionStages.leanに12公開宣言を実装した。
既存raw包Bのn段にULift Bの型を与え、係数射をφ_B^n∘jとして実Algebra構造を定義した。
δ係数射のFrobenius自然性から、係数像がj(φ_A^n(a))そのものであることを証明した。
既存DeltaPerfectionの第0段とjの合成を余極限の係数射として採用し、
第n段からの実標準射が全て同じ係数像を与えることをdeltaPerfectionOf_iterateから証明した。
これにより第n段から実完全化へのAlgHomと、隣接Frobenius遷移AlgHomを構成し、
両者の合成が第n段の標準AlgHomに一致する可換図式を証明した。
任意δ環・任意σを許し、p正則性・完全性・完備性はこの図式に要求しない。
既存の完全化・環の余極限を再利用し、同等の構成を増設していない。
対象3870ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2084報告成功。
標準3公理のみ、新sorry・公理・引用なし。共有・CLMST・利用先は編集せず追加送信も行っていない。
次の完全化側の証明は、完全係数環のφ_A^nが自己同型であることを使った全段CFFと、
正確な剰余テンソル・逐次余極限の比較である。今回の係数図式だけで完全化後CFFは結論しない。
G9最終API、実完備化の離散性、候補環CFF、一般B4は引き続き未完成として保持する。

## 完全係数環上のFrobenius各段の完全忠実平坦性の計画（2026-10-16）

BS担当でDeltaRootPerfectionStageFlat.leanを新設する。
既存の実段型・係数作用を保持し、完全係数環のφ_A^nをmod p環自己同型へ降下する。
係数商のULiftコピーを介し、段の実剰余を既存raw p商と比較して作用の塔を証明する。
Mathlibの忠実平坦性の推移性を使い、各段の正確な通常剰余テンソルの忠実平坦性を得る。
全段のp正則性を供給し共通G3で全段のp完全忠実平坦性を証明する。
一般のスカラー変更・余極限補題はBS内で新設せず、具体的段の比較として実装する。
ビルド・BS専用依存監査後に個別コミットする。

## 実Frobenius全段のp完全忠実平坦性（2026-10-16）

DeltaRootPerfectionStageFlat.leanに3公開定理を実装した。
既存のn段型・係数作用φ_B^n∘jをそのまま用い、実剰余S_n/(p)をULift環同型に沿って
既存raw B/pと比較した。完全係数環のφ_A反復の全単射性から、A/pの実自己同型を構成した。
係数商のULiftコピーKを、この自己同型でA/p上の代数とした。
Kから既存raw p商への作用、Kから実段剰余への作用を明示して、環比較をK線形にした。
代表元ごとの係数式からA/p→K→実段剰余の塔を証明し、忠実平坦性の推移性で
実段剰余・正確な通常剰余テンソルのA/p忠実平坦性を得た。
ULift標準作用とFrobeniusを持つ作用の混同を防ぐため、使用するSMul・Moduleを局所で明示した。
raw包のp正則性を元のAのpスカラーに直して、共通G3から全n段のp完全忠実平坦性を証明した。
入力は完全δ環・任意元族・指定単元δp。Noether性・有限生成性・完備性を追加せず、n=0も含む。
対象3871ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2087報告成功。
標準3公理のみ、新sorry・公理・引用なし。自分のBS専用変更だけを個別コミットする。
全段CFFと、実Frobenius余極限全体のCFF・p完備化後のCFF・一般B4完成は区別する。
次は実余極限の正確なA加群図式と通常剰余テンソルの比較へ進む。共通G9の最終APIは未完成。

## 実δ完全化と正確なA加群直極限の比較計画（2026-10-16）

BS担当でDeltaRootPerfectionModuleLimit.leanを新設する。
既存の実段型・係数作用を保持して任意i≤jのφ^(j-i)遷移AlgHomを構成し、
実完全化への標準AlgHomとの可換性を証明する。
この具体的A線形直系のModule.DirectLimitを既存DeltaPerfectionのA加群へ写す。
単射性は環直極限の零元の有限段消滅判定、全射性は実環直極限の段代表元表示を用いる。
段の標準射の単射性やFrobenius自体の単射性は仮定しない。
両直極限の標準像を保つ線形同値を公開し、後の通常剰余テンソル比較・平坦性移送へ使う。
一般直極限はMathlibを再利用し、共通の一般補題は重複作成しない。
対象ビルド・BS専用監査後に個別コミットする。

同工程で、既存MathlibのTensorProduct.directLimitLeftを線形同値に合成し、
任意A加群Nについて実δ完全化⊗_A Nと全段のS_n⊗_A NのModule.DirectLimitを比較する。
各段の標準純テンソルの像も証明し、後の平坦性・忠実性移送で元の射を追跡できるようにする。

## 実δ完全化のA加群直極限・通常テンソル比較（2026-10-16）

DeltaRootPerfectionModuleLimit.leanに10公開宣言を実装した。
既存実段S_nに任意i≤jのφ_B^(j-i)遷移AlgHomを与え、A線形直系条件と
既存実δ完全化への全段標準射との可換性を証明した。
具体的Module.DirectLimitから既存DeltaPerfectionへの標準線形射を構成した。
単射性では、環直極限で零になる実段の元が後の段で零になる判定を使い、
加群直極限の標準像の関係式へ戻した。全射性では実環直極限の段代表元表示を使った。
Frobeniusや各段から余極限への標準射の単射性を追加せず、線形同値と全段の標準像の式を得た。
MathlibのTensorProduct.directLimitLeftを合成し、任意A加群Nについて
実完全化⊗_A Nと各S_n⊗_A Nの具体的Module.DirectLimitとの線形同値を公開した。
各実段の標準純テンソルの像も証明し、平坦性・忠実性検出に元の射を使用できる。
任意δ係数環・任意根族を許し、完全性・p正則性・完備性は比較自体の仮定ではない。
対象3872ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2097報告成功。
標準3公理のみ、新sorry・公理・引用なし。高いheartbeat設定は不要になり除去した。
自分のBS専用変更だけを個別コミットし、共有・CLMST・利用先は編集せず追加送信も行っていない。
次は全段の正確な剰余平坦性・忠実性をこの実直極限比較へ適用し、余極限のCFFへ進む。
実余極限自体のCFF、完備化後の候補CFF、一般B4全射性、G9最終判定は未完成として保持する。

## 実δ完全化の標準剰余平坦性への移送計画（2026-10-16）

BS担当でDeltaRootPerfectionResidueFlat.leanを新設する。
完全係数環・指定単元δpの下で、A/p加群の単射について全段テンソルの単射性を
既存の完全平坦性とTor1判定から供給する。実テンソル直極限比較と零元の有限段消滅を使い、
同じ単射性を実完全化へ移す。通常の商テンソル消去で、正確な(A/p)⊗_A CのA/p平坦性を証明する。
一般の直極限平坦性・係数変更判定は新設せず、BSの具体的実段図式に適用する。
忠実性・CFF全体は次に単位を保つ実段射の零性検出と合わせて証明する。
対象ビルド・BS全依存監査後に個別コミットする。

## 実δ完全化の通常剰余テンソルの平坦性（2026-10-16）

DeltaRootPerfectionResidueFlat.leanに3公開定理を実装した。
A/p加群の単射fについて、各実段S_nとの通常Aテンソルの単射性を証明した。
fの余核はpで消えるため、全段CFFの完全平坦性から必要なTor1消滅を得て、
既存のTor1による単射性判定へ適用した。任意の両立するA作用とA/p作用を明示する。
実段テンソル直系上のfの直極限射を構成し、零元が後の段で消える判定と
各段テンソル単射性から直極限射の単射性を得た。前工程の実テンソル比較と
標準純テンソルの式で自然性を証明し、実δ完全化Cとの通常Aテンソルへ戻した。
最後に共通の通常商テンソル消去を使い、正確な(A/p)⊗_A CのA/p平坦性を証明した。
遷移射自体の平坦性・単射性や、直極限標準射の単射性は要求していない。
入力は完全δ係数環・任意元族・指定単元δp。Noether性・有限生成性・完備性を追加しない。
対象3875ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2100報告成功。
標準3公理のみ、新sorry・公理・引用なし。自分のBS専用変更のみを個別コミットする。
次は単位を保つ実段射を使った剰余テンソルの忠実性検出とG3への合流。
実余極限CのCFF・完備化後候補CFF・一般B4・G9最終APIは未完成として区別する。

## 実δ完全化の剰余忠実性・完全忠実平坦性の計画（2026-10-16）

BS担当でDeltaRootPerfectionFaithful.leanを新設する。
各実段の通常mod pテンソルの忠実平坦性から、A/p加群Nへの1⊗写像の単射性を
通常テンソル消去で得る。実テンソル直極限で1⊗xが零なら、後の実段で1⊗xが零となる。
段遷移の実AlgHomが単位を保つことと段の単射性からx=0を得て、実完全化の1⊗写像の単射性を証明する。
既証剰余平坦性と零性検出から通常mod pテンソルの忠実平坦性を得る。
既存実δ完全化の完全性からp正則性を供給し、G3で実完全化自体のp完全忠実平坦性へ合流する。
段遷移自体の平坦性・単射性は仮定せず、既存完全化・完全平坦性APIを再利用する。
対象ビルド・BS専用監査後に個別コミットする。

同工程で既存PerfectPrismRootRawFlat.leanへ、完全prismと任意元族のみを入力にする
実δ完全化のp完全忠実平坦性の入口を追加する。既存の内部δp単元供給と
今回の実余極限CFFを合成し、新しい単元・ghost仮定を利用側へ渡さない。

## 実δ完全化のp完全忠実平坦性への合流（2026-10-16）

DeltaRootPerfectionFaithful.leanに5公開定理を実装した。
各実段S_nについて、正確な剰余テンソルの忠実平坦性と通常テンソル消去を合成し、
A/p加群Nへの1⊗写像N→S_n⊗_A Nの単射性を証明した。
実完全化Cで1⊗xが零なら、実テンソル直極限比較により第0段の1⊗xが直極限で零となる。
零元の有限段消滅を使い、後の段の遷移AlgHomが単位を保つため1⊗x=0を得る。
その段の既証単射性からx=0を得て、N→C⊗_A Nの単射性を証明した。
これを通常商テンソル消去と合わせ、実(A/p)⊗_A Cの忠実平坦性を得た。
既存DeltaPerfectionの完全性によるp正則性を、元のAのpスカラーについて表し、
共通G3でdeltaRootPerfection_isCompletelyFaithfullyFlatへ合流した。
一般δ完全化の同等定義や、一般の余極限・忠実平坦性補題は新設していない。
完全δ係数環・任意元族・指定単元δpを入力とし、遷移射の平坦性・単射性は要求しない。
既存PerfectPrismRootRawFlat.leanへも1公開定理を追加し、完全prismと任意元族のみから
同じ実δ完全化のp完全忠実平坦性を供給した。δpの単元性は従来の内部補題で供給する。
対象3876・完全prism入口3884ジョブ成功（共有既存警告のみ、自分のコード警告なし）。
pure B4監査2106報告成功、標準3公理のみ、新sorry・公理・引用なし。
自分のBS専用変更のみを個別コミットし、共有・CLMST・利用先は編集せず追加送信も行っていない。
次は既存p進完備δ完全化へのCFF保存と、元の導来(p,d)候補・perfectoid商との接続を検証する。
今回の実δ完全化CのCFFと、p進完備化後の候補CFF・一般B4全射性の完成は区別する。
既存André引用・B-I/B6引用は使わず、削除・弱化もしていない。G9最終APIは未完成。

## 既存p進完備δ完全化へのCFF保存の計画（2026-10-16）

BS担当でDeltaRootPCompletedPerfectionFlat.leanを新設する。
既存PCompletedDeltaPerfection Fをそのまま使い、実raw係数射との合成をA作用として固定する。
共通adicCompletionOpenQuotientEquivをp主イデアルに適用し、
元のA/pに関する正確な商環と通常剰余テンソルを、完備化前後で比較する。
標準係数像を保つ式を証明し、それからA/p線形性を確認して忠実平坦性を移す。
既存のp進完備δ完全化の完全性でp正則性を供給し、共通G3でCFFを証明する。
同工程で完全prismからの追加入力不要の公開入口も既存BS専用ファイルへ追加する。
一般adic完備化の保存補題は重複実装せず、Noether性・有限生成な環は仮定しない。
この候補のCFFと、元の実導来(p,d)候補との比較・最終perfectoid商のCFFは別工程として保持する。
対象ビルド・BS専用監査後に個別コミットする。

## 既存p進完備δ完全化のp完全忠実平坦性（2026-10-16）

DeltaRootPCompletedPerfectionFlat.leanに15公開宣言を実装した（局所登録の4構造も専用監査対象）。
既存PCompletedDeltaPerfection Fを使い、元のraw係数射と既存標準射の合成を実A作用にした。
完備化前Cからの標準Algebra構造を明示して、元の係数射との合成式を証明した。
共通adicCompletionOpenQuotientEquivをJ=(p:C)に適用し、正確なA係数の実p商を前後で比較した。
この環同型が元のCの標準完備化像をCの元の標準商像へ戻す式を証明した。
A/pの両商への作用・Module構造を局所で明示し、係数像の式からA/p線形性を証明した。
既存の通常商テンソル比較を合成し、(A/p)⊗_A Zと(A/p)⊗_A Cを正確に比較して忠実平坦性を移した。
既存p進完備δ完全化の完全性からp正則性を供給し、共通G3でZのp完全忠実平坦性を証明した。
さらにPerfectPrismRootRawFlat.leanへ1公開定理を追加し、完全prismと任意元族のみで適用可能にした。
Noether性・有限生成な環は仮定せず、必要な有限生成性はp主イデアルについて共通APIへ供給する。
対象3929・完全prism入口3937ジョブ成功（共有既存警告のみ、自分のコード警告なし）。
pure B4監査2122報告成功、標準3公理のみ、新sorry・公理・引用なし。
自分のBS専用変更だけを個別コミットし、共有・CLMST・利用先は編集せず追加送信も行っていない。
対象はFrobenius根関係φ(r)/pのraw p除算包の既存p進完備δ完全化である。
このCFFだけで元のr/d包との同型や、d商での実両立根の存在を結論しない。
元の実導来(p,d)対象との比較・離散性（G9）、r/dによる最終prism候補のCFF、
そのperfectoid商、一般B4全射性は引き続き未完成として区別する。
実導来完備化を古典的完備化へ無条件に置き換える変更はしていない。

## 元のr/d対象への完全prism入力供給計画（2026-10-16）

BS担当でPerfectPrismRootSourcePowerInputs.leanを新設する。
対象は元のDeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator bであり、
φ(r)/pのraw包の完全化へ置き換えない。現在の単根工程[Unique σ]を明示する。
完全prismからp正則性・生成元正則性・δd単元性を供給し、各n>0の生成元冪商T=A/(dⁿ)について
実T対象のp導来完備性、標準mod p実還元の全非零次数消滅・H0忠実平坦性を供給する。
既存DistinguishedPowerTorsionによりTのp冪ねじれがpⁿで消える評価も同じ公開入力へまとめる。
共通G9-4の実冪余核モデル比較に適用し、選択した元の射影モデルのp余核複体の次数消滅も証明する。
G9の最終離散性判定は共通担当の完成を待ち、同等の一般判定をBSに新設しない。
対象ビルド・BS依存監査後に個別コミットする。

## 元のr/d実対象に対する完全prismからのG9入力（2026-10-16）

PerfectPrismRootSourcePowerInputs.leanに4公開定理を実装した。
対象は元のDeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator bそのものであり、
φ(r)/pのraw包やその完全化との同型を仮定・主張していない。
完全prismから係数p正則性、生成元d正則性、δd単元性を内部供給し、各n>0について
実T=A/(dⁿ)還元のT上p導来完備性、標準mod p実還元の全非零次数消滅とH0忠実平坦性を公開した。
Tのp冪ねじれがpⁿで消える既存評価も、perfectPrismRootSourcePower_G9_inputsにまとめた。
T自体のp正則性・pねじれのなさは要求せず、一般のねじれを許す生成元冪商を扱う。
共通G9-4のpowerCokernel_homology_isZero_of_reductionを同じ実T対象へ適用し、
選択した元の上有界射影モデルのp余核複体の非零次数ホモロジー消滅も証明した。
p^1=pは、係数環商と実導来対象全体の型族に沿って等式輸送し、別の商作用を混同していない。
現在の単根工程[Unique σ]を明示し、一般元族への完成とは数えない。
対象3920ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2126報告成功。
標準3公理のみ、新sorry・公理・引用なし。共通G9-4の既存証明済みAPIに依存する。
共有の未コミット・未追跡共通ファイルはそのまま利用・検証し、自分のBS専用変更のみをコミットする。
共通G9の一般離散性判定はなお未完成。今回の次数消滅は標準mod p還元とp余核複体についてであり、
元の実T対象自体の離散性やH0の有界ねじれ、候補CFF、一般B4を完成とはしない。
共有・CLMST・利用先は編集せず、他チャットへの追加送信も行っていない。

## 元の実導来源からraw r/d包への比較射の計画（2026-10-16）

BS担当でDeltaRootSourceRawComparison.leanを新設する。
元の実二因子導来テンソルの標準augmentationと、既存deltaDivisionSourceTensorEquivを接続する。
通常テンソル・raw包の正確な実源L作用を照合し、元の実源からraw次数零対象への標準射とH0比較を公開する。
元のAへの係数制限後の射を、既存p,d逐次実導来完備化関手で送り、
DeltaRootSourceIteratedPDCompletionからraw係数制限対象の同じ逐次完備化への比較射を構成する。
標準p,d合成完備化単位との可換性を関手の自然性で証明する。
高次Tor消滅やG9離散性を仮定・結論せず、比較射が同型であるとは数えない。
raw対象の完備化と既存prism候補との比較は後続工程とし、古典的完備化への置換を行わない。
対象ビルド・BS専用監査後に個別コミットする。

## 元の実導来源とraw r/d包の標準augmentation・逐次完備化比較射（2026-10-16）

DeltaRootSourceRawComparison.leanに11公開宣言を実装した。
raw r/d包へ評価βを経由する実源L作用を明示し、既存の通常テンソル・raw包の環同型をL線形にした。
元の二因子実導来テンソルの標準augmentationをこの比較へ合成し、raw次数零対象への標準射を構成した。
実源L上のH0同型と、標準augmentationがH0同型を誘導することを証明した。
同じ実係数制限で、元のA上の実源からraw係数制限次数零対象への射とA上のH0同型も公開した。
この射に元と同じ既存p,d逐次実導来完備化関手を適用し、
DeltaRootSourceIteratedPDCompletionからraw係数制限対象の同じ実逐次完備化への標準比較射を構成した。
p,d合成標準完備化単位との可換性を、二つの既存完備化単位の自然性から証明した。
比較自体では[Unique σ]が不要であり、任意σについて実装した。p正則性・distinguished性・完備性も仮定しない。
対象3855ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2137報告成功。
標準3公理のみ、新sorry・公理・引用なし。共有・CLMST・利用先は編集せず追加送信も行っていない。
ここでのH0同型は完備化前の実源についてであり、高次Tor消滅や実源全体の離散性は結論しない。
完備化後の比較射の同型性、raw係数制限対象の完備化と既存prism候補の比較、
候補の完全忠実平坦性・一般B4全射性・G9最終判定は未完成として保持する。
φ(r)/pの別raw包へ置き換えず、r/d由来の元の二因子実源と既存raw包を実標準射で接続した。
自分の検証済みBS専用変更のみを個別コミットする。

## raw r/d包の標準A作用と既存候補への射の計画（2026-10-16）

BS担当でDeltaRootSourceRawCoefficients.leanを新設する。
評価βを経由して制限したraw包のA作用を、元のAからの標準係数作用と恒等線形同型で照合する。
実次数零対象・H0の比較も、標準A加群としてのraw環へ移す。
既存deltaRootPrismCoefficientMapで候補へのA作用を固定し、既存deltaRootPrismRawMapをA線形射にする。
元の実導来源のaugmentationと係数比較にこの射を合成して、
既存prism台環候補の次数零対象への標準射を構成する。
この段階では標準射の構成のみとし、候補への完備化後延長・同型性・CFFは別工程とする。
共通係数制限APIを再利用し、対象ビルド・専用監査後に個別コミットする。

## 元の実導來源から既存prism台環候補への標準射（2026-10-16）

DeltaRootSourceRawCoefficients.leanに7公開宣言を実装した。
評価βを経由して係数制限したraw r/d包のA作用を、標準A作用と恒等線形同型で照合した。
sourceEval_Cによりβ(C(Ca))=C(a)を使い、標準Algebra作用の等式で既存raw環の作用へ戻した。
係数制限後のraw次数零対象と標準A作用付きraw環の次数零対象の実導来同型、
元の実導來源のH0と標準raw環のA線形同型を公開した。
既存deltaRootPrismCoefficientMapのA代数構造を明示し、既存deltaRootPrismRawMapをA線形射へ束ねた。
候補台環を同じ係数作用で次数零に置き、元の実二因子源のaugmentation・係数比較・
既存raw環射を合成してdeltaRootSourceCandidateMapを構成した。
候補のCommRing・A代数・A加群構造を各データ定義で明示し、別の作用を暗黙に採用していない。
任意δ環・任意添字族σを許し、p正則性・distinguished性・完備性・Unique σは要求しない。
対象4040ジョブ成功（共有既存警告のみ、自分のコード警告なし）、pure B4監査2144報告成功。
標準3公理のみ、新sorry・公理・引用なし。自分のBS専用変更のみを個別コミットする。
次は候補次数零対象の元のA上のp,d導来完備性を照合し、標準源射を実逐次完備化から延長する。
その延長の同型性・候補CFF・一般B4全射性と、G9最終判定は未完成として保持する。
共有・CLMST・利用先は編集せず、他チャットへの追加送信も行っていない。

## 既存候補のA上完備性と実逐次完備化からの一意延長の計画（2026-10-16）

BS担当でDeltaRootSourceCandidateCompletion.leanを新設する。
既存prism台環候補のH0自身のp・標準生成元像導来完備性をPDCompletionInterfaceから取得する。
既存isModuleComplete_algebraMap_iffで、標準A係数作用についてのp,d導来完備性へ移す。
元の実導来源からのdeltaRootSourceCandidateMapに共通derivedComplexCompletionHomEquivを二回適用し、
実p完備化・実p,d逐次完備化から候補次数零対象への標準射を構成する。
各標準単位・合成単位との可換性と、合成単位上で一致する射の一意性を証明する。
新しい一般反射・完備化は作らず、候補への比較射の同型性・CFFをこの一意延長だけから結論しない。
対象ビルド・BS専用監査後に個別コミットする。

## raw経由と直接延長の比較計画（2026-10-16）

BS担当でDeltaRootSourceCandidateFactorization.leanを新設する。
raw係数次数零対象から既存候補への射を既存線形射で明示し、p,d完備性による一意延長を構成する。
元の実逐次完備化源からrawの実逐次完備化への比較射との合成が、直接構成した候補延長射に等しいことを、
標準単位図式と既証の一意性で証明する。G9の最終離散性判定を待たずに行う。
この因子分解から比較射の同型性・完全忠実平坦性は結論しない。ビルド・BS監査後に別コミットする。

## 候補のA上完備性と一意延長の実装結果（2026-10-16）

DeltaRootSourceCandidateCompletion.leanの9公開宣言を実装した。
既存候補のA上のp,d導来完備性を既存PDCompletionH0と係数制限APIから証明し、
元の実二因子源からの標準射を実p完備化と実p,d逐次完備化へ一意に延長した。
各単位図式と合成単位に関する存在一意性も証明済み。任意δ環・任意添字族を許す。
対象4043ジョブ成功、自分のコード警告なし（共有既存警告のみ）。
pure B4監査2153宣言成功、標準3公理のみ、新sorry・公理・引用なし。
比較射の同型性・候補CFF・一般B4全射性は引き続き未完成。G9全体も共有計画では未完成。

## raw経由と直接延長の比較の実装結果（2026-10-16）

DeltaRootSourceCandidateFactorization.leanに8公開宣言を実装した。
raw係数次数零対象から既存候補への具体的A線形由来の射を定義し、
元の実導来源からの標準射がそのraw射を経由することを証明した。
raw射を実p完備化・実p,d逐次完備化から延長し、各単位図式を証明した。
元の実逐次完備化からrawの実逐次完備化への既存比較射とraw延長の合成が、
直接のdeltaRootSourceCandidateIteratedMapに等しいことを一意性で証明した。
対象4044ジョブ成功、自分のコード警告なし（共有既存警告のみ）。
pure B4監査2161宣言成功、標準3公理のみ、新sorry・公理・外部引用なし。
この因子分解は同型性を主張しない。候補はrawにδ完全化・p進完備化も施しており、
rawの逐次導来完備化との一致は別途証明を要する。G9最終判定・候補CFF・一般B4は未完成。
共有ファイル・利用先を変更せず、他チャットへの追加メッセージも送っていない。

## 任意有限根族の次段Witt残余Koszul計画（2026-10-16）

BS担当でDeltaDivisionFiniteWittFamilyKoszul.leanを新設する。
既存の有限正規化実源商における最高段有限族の弱正則性を、後続多項式環への平坦基底変更で移す。
既存NormalizedAmbientSourceEquivとFiniteNormalizedQuotientEquivを使い、
元の相対自由δ環のmod(p,d)・下位関係商上で異なる有限個の次段Witt関係の弱正則性とKoszul分解を証明する。
Unique σを仮定せず、p正則性・ghost単射・δdの指定単元を明示する。
この段階はWitt関係族までで、元のδ反復関係族への同時置換と全有限深さの統合は次段階とする。
G9の一般判定は重複実装しない。対象ビルド・BS監査後に自分の変更のみをコミットする。

## 任意有限根族の実δ次段関係への置換計画（2026-10-16）

BS担当でDeltaDivisionFiniteJetFamilyKoszul.leanを新設する。
実下位関係商内で各δ次段関係とWitt関係が同じ主イデアルを生成する既証等式を使う。
有限prefixの生成イデアルも一致することを示し、次段Witt有限族の弱正則性を実δ反復関係族へ移す。
有限族全体のKoszul分解を公開し、Unique σなしで複数根を扱う。
全δ深さの連結・導来源への適用・候補CFFとは区別し、ビルド・監査後に別コミットする。

## 任意有限根族の次段Witt残余Koszulの実装結果（2026-10-16）

DeltaDivisionFiniteWittFamilyKoszul.leanに4公開定理を実装した。
有限正規化実源商の最高段有限族を、Mathlibの弱正則列の平坦基底変更で後続多項式環へ移し、
既存二つの商比較同型により元の自由δ環の実mod(p,d)・下位関係商へ戻した。
任意の異なる有限根族について次段Witt関係の弱正則性と実Koszul分解を証明済み。
Unique σ・σ全体の有限性は不要。p正則性・ghost単射・δd指定単元は明示している。
対象3749ジョブ成功、自分の警告なし。pure B4監査2165宣言成功、標準3公理のみ。
新sorry・公理・引用なし。元のδ関係族への同時置換・全有限深さの統合・G9・候補CFF・一般B4は別工程。

## 任意有限根族の実δ次段関係Koszulの実装結果（2026-10-16）

DeltaDivisionFiniteJetFamilyKoszul.leanに2公開定理を実装した。
元のmod(p,d)・下位δ関係商で各次段δ反復関係とWitt関係が同じ主イデアルを生成することを使用し、
任意の有限prefixの生成イデアルも一致することを証明した。
各prefix商でWitt関係の正則性をδ関係へ移し、異なる任意有限根族の次段δ関係が弱正則であることと、
その実Koszul分解を証明した。Unique σ・σ全体の有限性は要求しない。
p正則性・実自由δ環のghost単射・δd指定単元を明示した一般除算の結果である。
対象3750ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2167宣言成功。
標準3公理のみ、新sorry・公理・引用なし。新規2モジュール・計画・BS専用監査だけを変更した。
次は根関係の深さ0有限族の残余Koszulを用意し、有限添字集合上で各深さの関係族を連結する。
連結prefixの生成イデアルを実有限関係イデアルへ同定した後、既存の実有限源Tor・逐次colimitへ接続し、
一元性が残る実導來源の計算を拡張する。今回の次段有限族だけで全深さ・任意根族の源Tor消滅を結論しない。
G9最終判定、比較射の同型性、候補CFF、一般B4全射性は引き続き未完成。

## 深さ0の任意有限根族の実残余Koszul計画（2026-10-16）

BS担当でDeltaRootFirstResidueFamilyKoszul.leanを新設する。
DeltaRootFirstEvaluationKoszul.leanの既存private負号補題を再利用するため、
負のモニック根関係の有限族についての公開定理を同ファイルへ追加する。
mod(p,d)で係数多項式商と自由δ多項式商を既存商同型で比較し、
最初のδ関係が負の根関係の係数像となることから任意有限族の弱正則性・Koszul分解を証明する。
δ構造を不変でない商へ降ろさず、完備性・ghost・Unique σは要求しない。
その後、有限根添字を全列挙して各深さの関係族を連結する工程へ進む。
対象ビルド・BS専用監査後、自分の変更のみを個別コミットする。

## 有限根添字の全δ深さの連結計画（2026-10-16）

BS担当でDeltaDivisionFiniteFamilyResidueKoszul.leanを新設する。
有限根添字をFin mで全列挙し、深さ0からNまでの実mod(p,d)関係リストを深さ順の連結として定義する。
リストの元の特徴づけから生成イデアルを既存deltaDivisionFiniteRelationIdealの実商像へ同定する。
既存の二重商比較を使い、深さ1の有限族と既証の次段δ有限族を連結前段商上の弱正則性へ戻す。
初項族の弱正則性から全有限深さの弱正則性を証明し、根関係については初項入力も供給する。
この有限添字での全深さ結果と、無限根族のfiltered colimit・実導来源の全Torは区別する。
対象ビルドとBS専用監査後に別コミットする。

## 深さ0任意有限根族の実残余Koszulの実装結果（2026-10-16）

DeltaRootFirstEvaluationKoszul.leanの既存負号補題から、負のモニック根関係の有限族の公開定理を追加した。
DeltaRootFirstResidueFamilyKoszul.leanで、係数多項式商・自由δ多項式商の標準同型と
Mathlibの平坦基底変更を使い、深さ0の実根δ関係の任意有限族の弱正則性とKoszul分解を証明した。
δ構造を商へ降ろさず、p正則性・ghost単射・完備性・Unique σを仮定しない。
対象3760ジョブ成功、自分のコード警告なし。pure B4監査2170宣言成功、標準3公理のみ。
新sorry・公理・引用なし。全δ深さの連結、源Tor、候補CFF、一般B4は引き続き別工程。

## 有限根族の全δ深さの実残余Koszulの実装結果（2026-10-16）

DeltaDivisionFiniteFamilyResidueKoszul.leanに8公開宣言を実装した。
有限根族をFin mで全列挙してδ深さ順の実mod(p,d)関係リストを構成し、長さm(N+1)と元の特徴づけを証明した。
生成イデアルが既存deltaDivisionFiniteRelationIdealの実商像と一致することを証明した。
この一致と二重商の標準同型を使い、深さ1および一般次段の有限族の弱正則性を、連結列の前段商へ戻した。
初項族の弱正則性を仮定した一般除算の全有限δ深さの弱正則性・実Koszul分解を公開した。
根関係族に対しては深さ0の入力とG4のghost単射を内部で供給し、元の係数のp正則性とδd指定単元のみで
全有限δ深さの実残余弱正則性・Koszul分解を証明した。Unique σは不要で、空の有限添字も許す。
対象3765ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2178宣言成功。
標準3公理のみ、新sorry・公理・引用なし。
次は深さ順に連結した座標族について、元の反復δ関係から実評価関係への移送を複数根に拡張し、
既存の源グラフ商のTor同型へ接続する。現時点では反復δ関係のKoszul分解であり、実評価列の分解は別途必要。
無限根族のfiltered colimit、G9最終判定、候補比較の同型性、候補CFF、一般B4は未完成として保持する。

## 複数根の実評価関係への段階別移送計画（2026-10-16）

BS担当でDeltaDivisionEvaluationFamilyStep.leanを新設する。
DeltaDivisionFiniteEvaluationRelations.leanの既存private pairイデアル比較を一根ごとに再利用し、
全下位関係を課した後に次の実評価関係とδ反復関係が同じ主イデアルを生成することを公開する。
下位関係を消す任意の通常環射へこの等式を移し、有限prefixのイデアル一致により、
次段の任意有限δ関係族の弱正則性を実評価関係族へ移す。対象商にδ構造は要求しない。
その後、既証の有限根族全深さリストと、実源グラフ商のTor計算へ接続する。
ビルド・専用監査後に、自分のBS変更のみを個別コミットする。

## 有限根族の全深さ実評価列と源座標の計画（2026-10-16）

BS担当でDeltaDivisionFiniteFamilyEvaluation.leanを新設する。
有限根族・全有限δ深さを深さ順に列挙する座標リストを作り、長さ・含まれる座標・重複なしを証明する。
同じ座標上の反復δ関係は既存の全深さリストに一致することを照合する。
実評価関係リストの生成イデアルを実有限関係イデアルの商像と照合し、
前段商での段階別移送を帰納的に適用して全実評価列の弱正則性を証明する。
根関係について既証入力からKoszul分解を供給し、重複のない実座標を既存源グラフTor同型へ渡す。
有限根添字でのTorと、無限根族・全源評価環への逐次colimitを区別する。
対象ビルド・BS監査後に自分の変更のみをコミットする。

## 複数根の段階別実評価移送の実装結果（2026-10-16）

DeltaDivisionFiniteEvaluationRelations.leanに、一根の次段実評価関係とδ反復関係が、
全下位関係の後で同じイデアルを追加する公開定理を実装した。
既存のpairイデアル比較をUnit添字で一根ごとに使い、他の根の次段関係を混ぜていない。
DeltaDivisionEvaluationFamilyStep.leanで下位関係を消す任意通常射の後の主イデアル等式、
有限族の弱正則性の移送とKoszul分解を公開した。Unique σ・対象環のδ構造は不要。
対象2529ジョブ成功、自分のコード警告なし。pure B4監査2182宣言成功、標準3公理のみ。
新sorry・公理・外部引用なし。全深さ実評価列・源Tor・無限根族・G9・候補CFF・一般B4は別工程。

## 有限根族全深さ実評価Koszulと源Torの実装結果（2026-10-16）

DeltaDivisionFiniteFamilyEvaluation.leanに10公開宣言を実装した。
深さ順の実δ座標リストの元の特徴づけ・重複なしを証明し、そのδ反復関係像を既存全深さリストへ同定した。
同じ座標を実評価したリストの生成イデアルも、実有限δ関係イデアルの商像と一致すると証明した。
各段で元のδ列と実評価列の前段商を照合し、段階別移送により全深さ実評価列の弱正則性を証明した。
有限根添字の全列挙s : Fin m ≃ σについて、実mod(p,d)評価Koszul分解を公開した。
同じ重複のない実座標で源グラフ商を取り、実残余自由δ射に沿うTorとKoszulホモロジーの同型を構成した。
係数環のp正則性・δd指定単元から、全有限δ深さの実源グラフ商の正次数Tor消滅を証明した。
Unique σ・外部ghost単射入力は不要。空の有限根添字も許し、通常環射・実通常商を明示している。
対象3767ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査は全2195宣言成功。
内訳は標準公理使用2191報告、公理なし4報告。#print axioms全行数とも照合した。
以前の監査件数記録はdepends on axioms報告のみを集計しており、公理なし報告を含めていなかった。
今回の新しい座標定義も公理を一切使わないため、以後は両形式を数えて宣言総数を記録する。
標準3公理以外なし、新sorry・公理・外部引用なし。
次は有限根添字の源グラフ商の逐次colimitを実評価環へ同定し、G7を供給して全源のTor消滅へ進む。
無限根族へのfiltered colimit、G9最終判定、候補比較同型、候補CFF、一般B4全射性は未完成。

## 有限根族の実評価環への逐次colimit計画（2026-10-16）

BS担当でDeltaDivisionFamilySourceEvaluationColimit.leanを新設する。
有限根添字の全列挙s : Fin m ≃ σと既証の重複なし全深さ座標を使い、実有限源グラフ商を取る。
各有限グラフイデアルを分母1の既存有限δ関係イデアルへ同定し、その上限を実β評価核へ同定する。
標準商遷移・β評価射で逐次図式と余錐を作り、実評価環への普遍性と標準射可換なcolimit同型を証明する。
既存一元APIは保持し、同じ商・評価環を扱う有限添字版をBS側で供給する。
続いてG7をこの具体的図式へ適用し、有限段のTor消滅を全源評価環へ渡す。
ビルド・BS依存監査後に自分の変更のみを個別コミットする。

## 有限根族の全源Tor消滅へのG7接続計画（2026-10-16）

BS担当でDeltaRootFamilySourceColimitTor.leanを新設する。
有限根族の源グラフ逐次図式へ共通torAlg_preservesSequentialColimitsを適用し、
実colimit同型を通じて有限段の正次数Tor消滅を実評価環へ移す。
根関係族について既証の全有限δ深さTor消滅を供給し、p正則性とδd指定単元のみで全源の残余Tor消滅を証明する。
外部PreservesColimit・ghost単射入力を残さず、実β係数作用を型に明示する。
無限根族・G9・候補CFF・一般B4は別工程として保持する。ビルド・BS監査後に別コミットする。

## 有限根族の実源グラフ逐次colimitの実装結果（2026-10-16）

DeltaDivisionFamilySourceEvaluationColimit.leanに15公開宣言を実装した。
有限根添字s : Fin m ≃ σと全深さ座標で実有限源グラフ商を定め、グラフイデアルを分母1の既存有限δ関係へ同定した。
イデアルの上限が実β評価核であることを示し、標準商遷移・β評価射で具体的な逐次図式と余錐を構成した。
実評価環Aの普遍性を証明し、標準β射と可換な実圏論的colimit比較同型を公開した。
Unique σ不要、空の有限添字も許す。既存一元APIは保持し、共通層は編集していない。
対象3770ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2210宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。
次はG7をこの具体的図式へ供給し、有限段の実残余Tor消滅を全源評価環へ渡す。
無限根族への合流、G9最終判定、候補比較同型・CFF、一般B4は別工程として保持する。

## 有限根族の実導来評価とraw残余商の比較計画（2026-10-16）

BS担当でDeltaRootFamilyResidueSourceDerived.leanを新設する。
全源Tor消滅から共通boundedAboveDerivedBaseChangeModuleAugmentationIsoを適用する。
既存deltaRootResidueSourceEvalScalarEquivとdeltaDivisionSourceResidueTensorAlgEquivを再利用し、
実βに沿う残余終域の導来拡大を既存raw(p,d)商の次数零対象へ比較する。
順射が標準導来augmentationと具体的残余商比較の合成であることも公開する。
Unique σ・外部G7/ghost入力を加えず、標準写像を保持する。ビルド・BS監査後に別コミットする。

## 有限根族の全源Tor消滅の実装結果（2026-10-16）

DeltaRootFamilySourceColimitTor.leanに3公開定理を実装した。
共通G7を実有限根族の源グラフ逐次図式へ供給し、実評価環へのcolimit同型で有限段Tor消滅を全源へ移した。
根関係族についてp正則性とδd指定単元から有限段入力を供給し、実残余自由δ射に沿う全β評価環の正次数Tor消滅を証明した。
既存Tor対称性と導来base-changeホモロジー比較で、βに沿う実残余終域のscalarExtensionTorVanishingへ移した。
外部PreservesColimit・ghost入力は不要。有限添字の列挙sを明示しており、Unique σは要求しない。
対象3828ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2213宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。次は標準導来augmentationを既存raw残余商へ比較する。
無限根族、G9、候補比較同型・CFF、一般B4は未完成として保持する。

## 有限根族の実導来β拡大とraw残余商比較の実装結果（2026-10-16）

DeltaRootFamilyResidueSourceDerived.leanに2公開宣言を実装した。
有限根族の全源Tor消滅から共通の標準導来augmentation同型を適用し、
既存deltaRootResidueSourceEvalScalarEquivとdeltaDivisionSourceResidueTensorAlgEquivを再利用して、
実βに沿う残余終域の導来拡大と、既存raw(p,d)商の次数零対象との同型を構成した。
順射が標準導来augmentationと具体的残余商比較の合成に一致することも証明した。
有限列挙s : Fin m ≃ σ・元の係数のp正則性・δd指定単元を明示し、Unique σ・外部G7/ghost仮定は不要。
対象3838ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2215宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。既存係数同値や一般導来判定を重複定義していない。
次は元の二因子源の実三因子係数商還元へこの同型を結び、元の商係数環上のホモロジーと忠実平坦性を有限根族で供給する。
無限根族のfiltered colimit・G9・候補比較同型・CFF・一般B4は未完成として保持する。

## 有限根族の元二因子源の実係数商還元計画（2026-10-16）

BS担当でDeltaRootFamilySourceCoefficientResidue.leanを新設する。
既存DeltaRootSourceCoefficientReducedをそのまま使い、既存associator・実base-change/tensor比較と、
前段の有限根族の実導来β比較を合成して既存raw(p,d)商の次数零対象への同型を証明する。
同じ実対象のH0比較と非零次数ホモロジー消滅を公開する。
続いてDeltaRootFamilySourceQuotientFlat.leanを新設し、既存DeltaRootSourceQuotientDerivedと
係数制限・既存商作用を再利用して実商係数環上の消滅とH0同型、元のA/(p,d)上の忠実平坦性を証明する。
Unique σ・外部ghost/G7仮定を除いた有限根族の入力を用い、定義・一般判定・既存標準射は重複しない。
各段階のビルド・BS専用監査後に個別コミットする。無限根族・G9・候補CFF・一般B4は別工程。

同工程の補足：実商係数環上の次数零集中から、共通normalizedPureHomologyIsoで既存raw残余商のsingle比較も構成する。
そのH0が既証の商環線形同型そのものであることを、共通正規化のH0図式で照合する。
新たな離散化・同値の一般定義は作らない。

## 有限根族の元二因子源の実係数商還元の実装結果（2026-10-16）

DeltaRootFamilySourceCoefficientResidue.leanに3公開宣言を実装した。
既存DeltaRootSourceCoefficientReducedを再利用し、既存associator・実base-change/tensor比較と
有限根族の実導来β比較を合成して、元の二因子源の実三因子係数商還元を既存raw(p,d)商のsingleへ同定した。
同じ実対象のH0とraw残余商の比較、および非零次数ホモロジー消滅を証明した。
有限全列挙s : Fin m ≃ σ・元の係数のp正則性・δd指定単元を明示する。
Unique σ・外部ghost/G7仮定は不要。既存実対象・一般係数比較を重複していない。
対象3850ジョブ成功。後続対象からの最終再ビルドも成功し、自分のコード警告なし。
pure B4監査全2218宣言成功、標準3公理以外なし。新sorry・公理・外部引用なし。
次は同じ対象の実商係数環上の消滅・H0比較・元のA/(p,d)上の忠実平坦性へ進む。
無限根族・G9・候補比較同型/CFF・一般B4は未完成として保持する。

## 有限根族の実商係数環上の離散性・H0忠実平坦性の実装結果（2026-10-16）

DeltaRootFamilySourceQuotientFlat.leanに8公開宣言を実装した。
既存DeltaRootSourceQuotientDerived・商作用・係数制限を再利用し、元の実二因子源の商環還元で
非零次数ホモロジー消滅と、既存raw残余商との実商環線形H0同型を証明した。
元のA/(p,d)からの標準係数射による作用を、raw残余商の既存基底作用へ代表元上で照合し、H0忠実平坦性を証明した。
p正則性から実自由δ源のghost単射をG4で内部供給し、有限全列挙・p正則性・δd指定単元だけを入力にする。
標準t構造の次数零集中から共通normalizedPureHomologyIsoを適用してraw残余商singleとの比較を構成し、
そのH0が既証の具体的商環線形H0同型に一致することも証明した。Unique σ・外部ghost/G7仮定は不要。
対象3854ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2226宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。共有層・CLMST・利用先は変更していない。
次は既存の実係数商squareで、同じ結果を元のA/(p,d)上の実導来還元へ渡す。
有限根族の完備化後の比較・無限根族への合流・G9・候補比較同型/CFF・一般B4は未完成として保持する。

## 有限根族の元A係数への還元と逐次完備化後の還元計画（2026-10-16）

BS担当でDeltaRootFamilySourcePDResidue.leanを新設する。
既存deltaRootSourceCoefficientPDReductionIsoで実商係数環上の有限根族の結果を元A/(p,d)へ戻し、
raw商single比較・H0比較・非零次数消滅・H0忠実平坦性を同じ実係数還元で証明する。
続いてDeltaRootFamilySourceIteratedResidue.leanを新設し、既存DeltaRootSourceIteratedPDCompletionと
標準逐次完備化還元比較を使って同じ結果を実p,d逐次完備化後へ渡す。
pとdの個別正則性を明示し、raw比較と合成標準完備化単位の図式も保持する。
既存データ・一般係数比較・完備化は重複せず、各段階をビルド・BS監査後に個別コミットする。
無限根族・G9・候補比較同型/CFF・一般B4は別工程として保持する。

## 完全prismから有限根族の実逐次源への公開入口計画（2026-10-16）

BS担当でPerfectPrismRootFamilySourceInputs.leanを新設する。
完全な有向prism Pのp正則性、生成元のdistinguished性と正則性を既存APIから供給し、
有限根族の実p,d逐次完備化源について、元のA/(p,d)還元の次数消滅とH0忠実平坦性を証明する。
既存のp,d導来完備性も同じ実対象で束ね、追加ghost・δd単元・正則性入力なしの公開定理にする。
この入力は有限根族の実導来源に関するものであり、候補環のCFFや無限族への合流は結論しない。
対象ビルド・BS監査後に個別コミットする。

## 有限根族の元A/(p,d)還元の実装結果（2026-10-16）

DeltaRootFamilySourcePDResidue.leanに4公開宣言を実装した。
既存の実係数商squareを使い、実商係数環上のsingle比較を元A/(p,d)への実還元へ移した。
raw残余商singleとの比較、実H0比較、非零次数ホモロジー消滅、元A/(p,d)上のH0忠実平坦性を証明した。
有限全列挙s : Fin m ≃ σ・係数環のp正則性・δd指定単元を明示し、外部G7/ghost仮定は不要。
既存の実還元対象・係数射・一般squareを重複せず、Unique σは要求しない。
対象3859ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2230宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。次は同じ結果を実逐次完備化後へ渡す。
無限根族・G9・候補比較同型/CFF・一般B4は未完成として保持する。

## 候補への比較の目標の明確化（著者公開版再確認、2026-10-16）

著者公開版BS-prisms-author.pdfのLemma 3.9およびProposition 7.11(2)を再確認した。
原典はprismのperfectionをFrobeniusに沿うfiltered colimitとその導来完備化で構成し、
完全な基底上での平坦性をfiltered colimitを通じて移す。
未完全化の実源から既存完全候補へのcanonical mapは構成済みだが、その無条件の同型性は証明しておらず、
原典の接続にも要求されない。これを以後の完成条件として置かない。
必要な接続は、実源の離散性・環構造との比較、Frobenius各段の元A係数作用と実剰余平坦性、
その実filtered colimitおよび完備化と既存候補構成の照合である。
過去の記録の「候補比較同型」は、この完全化・δ完全化後の対象と候補台環の比較として精密化する。
未完全化のraw源をδ完全化後の候補へ同型とみなす置換は行わない。
今回の有限根族の実還元と忠実平坦性は、このfiltered colimit経路へ渡す元の実入力を供給する。
G9による離散性・d正則性や候補のCFFそのものは未完成として保持する。

## 有限根族の実逐次完備化後の還元の実装結果（2026-10-16）

DeltaRootFamilySourceIteratedResidue.leanに4公開宣言を実装した。
既存DeltaRootSourceIteratedPDCompletionと実還元比較を再利用し、p,dの個別正則性の下で
元A/(p,d)還元のraw商single比較・非零次数消滅・H0忠実平坦性を実p,d逐次完備化後へ移した。
raw比較と合成標準完備化単位の実還元図式も証明した。
有限全列挙s : Fin m ≃ σ・p正則性・d正則性・δd指定単元を明示する。
Unique σ・外部ghost/G7仮定は不要で、新たな完備化・係数還元対象は定義していない。
対象3867ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2234宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。次は完全prismからこの入力を追加仮定なく供給する。
無限根族・G9・perfection/完備化との比較・候補CFF・一般B4は未完成として保持する。

## 完全prismから有限根族の実逐次源への公開入口の実装結果（2026-10-16）

PerfectPrismRootFamilySourceInputs.leanに3公開定理を実装した。
完全有向prism Pのp正則性・生成元のdistinguished性・正則性を既存APIから取得し、
有限根族の元の実p,d逐次完備化源について、元A/(p,d)還元の非零次数消滅とH0忠実平坦性を証明した。
同じ実対象のp,d導来完備性も既存定理から束ね、perfectPrismRootFamilySource_complete_residue_inputsを公開した。
入力は具体的P・その完全性・根元族b・有限全列挙sだけで、追加の正則性・δd単元・ghost/G7仮定は不要。
Unique σ不要。新たな源・完備化・一般完全平坦性の定義は作っていない。
対象3878ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2237宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。
この結果は有限根族の実導来源に関する入力であり、未完全化源から完全候補への無条件同型性を主張しない。
次は有限根族のA/(dⁿ)上の標準mod p入力へG10比較を拡張し、共通G9への具体的入力を有限族で揃える。
Frobenius各段・filtered colimit・完備化を通じた既存候補のCFF、無限根族、G9最終適用、一般B4は未完成。

## 有限根族のG10・G9標準入力への拡張計画（2026-10-16）

BS担当でDeltaRootFamilySourceCanonicalPowerResidue.leanを新設する。
既存の冪零商・実基底変更の合成比較を再利用し、実A/(p,dⁿ)還元の標準冪零剰余を
既証の有限根族のA/(p,d)還元へ比較して、次数消滅とH0忠実平坦性を供給する。
次にDeltaRootFamilySourcePowerInputs.leanを新設し、共通G10で実A/(p,dⁿ)還元の離散性とH0平坦性を証明し、
既存の生成元冪商→標準mod p比較でA/(dⁿ)上の実標準mod p入力へ移す。
既存G8の商係数環上のp完備性も束ね、G9が要求する同じ具体的対象の入力を公開する。
G9に必要なのは各冪剰余H0の平坦性であり、今回は任意冪剰余の忠実性を追加の完成条件にしない。
元の(p,d)還元の忠実平坦性は既証のまま保持する。
最後にPerfectPrismRootFamilySourcePowerInputs.leanで完全prismから各入力と係数環のpⁿねじれ上界を供給する。
各段階のビルド・BS監査後に個別コミットし、共通G9の一般判定はBS側で重複実装しない。

## 有限根族の標準冪零還元入力の実装結果（2026-10-16）

DeltaRootFamilySourceCanonicalPowerResidue.leanに3公開宣言を実装した。
実A/(p,dⁿ)還元の標準冪零剰余を、既存の実基底変更の合成比較・標準商同型で元の実(p,d)還元へ接続した。
既存raw商singleとの比較、標準商環上での非零次数ホモロジー消滅・H0忠実平坦性を証明した。
途中の未公開補助的なpower比較を重複して作らず、既存の一般合成比較を直接再利用した。
有限全列挙・n>0・p,dの個別正則性・δd指定単元を明示し、Unique σ・外部G7/ghost仮定は不要。
対象3871ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2240宣言成功。
標準3公理以外なし、新sorry・公理・引用なし。次は共通G10で厚化前の実冪剰余対象を扱う。
G9最終適用・perfectionへのfiltered colimit・候補CFF・一般B4は未完成として保持する。

## 有限根族のG10とG9標準入力の実装結果（2026-10-16）

DeltaRootFamilySourcePowerInputs.leanに6公開定理を実装した。
既証の標準冪零還元の次数消滅・H0平坦性を共通G10へ供給し、実A/(p,dⁿ)還元の次数零集中とH0平坦性を証明した。
既存生成元冪商の標準mod p比較を使い、実A/(dⁿ)対象の標準mod p還元の非零次数消滅とH0平坦性へ移した。
既存G8の商係数環上のp導来完備性を同じ実対象で束ね、deltaRootFamilySourceGeneratorPower_G9_inputsを公開した。
有限全列挙・n>0・p,dの個別正則性・δd指定単元を明示する。Unique σ・外部G7/ghost仮定は不要。
今回はG9に必要な冪剰余H0の平坦性を証明し、元の(p,d)還元の忠実平坦性は既証として保持している。
対象3908ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2246宣言成功。
標準3公理以外なし、新sorry・公理・引用なし。次は完全prismから追加の係数環pⁿねじれ上界も供給する。
共通G9本体・その最終適用、perfection/完備化の比較、候補CFF・一般B4は未完成として保持する。

## 完全prismによる有限根族のG9入力供給の実装結果（2026-10-16）

PerfectPrismRootFamilySourcePowerInputs.leanに4公開定理を実装した。
完全prism Pの既存APIから正則性・δd指定単元を供給し、元の実逐次源のA/(dⁿ)還元について、
商環上のp導来完備性・係数環のpⁿねじれ上界・標準mod p実還元の次数消滅・H0平坦性を束ねた。
入力は具体的P・完全性・根元族b・n>0・有限全列挙sだけで、Unique σ・外部ghost/G7・追加正則性仮定は不要。
共通G9-4の比較を同じ実対象の選択射影モデルへ適用し、p余核複体の非零次数ホモロジー消滅も公開した。
対象3928ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2250宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。共通正本ではG9本体は引き続き未完了であり、入力供給と最終離散性を区別する。
G9待ちから独立した次工程は、完全基底δ環Aからのδ環射A→Bについて、
Bの実(p,d)還元の次数消滅・H0忠実平坦性を明示入力に置き、Frobeniusねじれ各段の係数作用と実還元を照合すること。
φ_A反復の係数商同型とmod pでのφ_Aⁿ(d)=d^(pⁿ)を使い、既存G10の冪零厚化比較を各段へ適用する。
その段階計算からδ完全化の実filtered colimit・既存候補の完備化へ忠実平坦性を渡す工程を進める。
元の実源の環としての離散性・G9最終適用・無限根族・候補CFF・一般B4は未完成として保持する。

## Frobenius各段の係数商比較計画（2026-10-16）

BS担当でPerfectDeltaPrismaticResidue.leanを新設する。
既存map_frobeniusLift_of_map_p_eq_zeroを反復し、pを消す通常射の下でφⁿ(x)=x^(pⁿ)を証明する。
(p,φⁿ(d))と(p,d^(pⁿ))のイデアル一致を証明し、完全係数δ環ではφⁿが誘導する
A/(p,d)≃A/(p,φⁿ(d))≃A/(p,d^(pⁿ))を標準代表元上の式とともに公開する。
この比較をFrobeniusねじれ段の正確な係数作用と、既存G10の実冪剰余比較へ渡す。
新たなFrobenius・商・一般導来底変換は定義せず、既存APIを再利用する。
対象ビルド・BS監査後に個別コミットする。G9・候補CFF・一般B4の完成とは区別する。

## G10による一般prism冪剰余の忠実平坦性の接続計画（2026-10-16）

BS担当でPrismaticPowerDerivedFlat.leanを新設する。
既存のprism冪剰余の実基底変更比較を合成して、標準冪零商の実還元と元のA/(a,d)還元を比較する。
元の実還元が次数零・H0忠実平坦であるという明示入力から、共通G10でA/(a,dⁿ)還元の次数零集中・H0平坦性を得る。
共通の正規化single比較・H0通常tensor比較・冪零作用に沿う忠実性判定を再利用してH0忠実平坦性も得る。
これはBSのprism冪剰余へのG10適用であり、G10本体・一般Tor/導来完備性判定は再実装しない。
a=p、n=p^kとFrobenius係数商同型を組み合わせ、後続の実Frobenius段係数比較へ使う。
対象ビルド・BS監査後に別コミットする。

## Frobenius各段の実係数商比較の実装結果（2026-10-16）

PerfectDeltaPrismaticResidue.leanに6公開宣言を実装した。
既存の一段Frobenius合同を反復し、pを消す通常射上でφⁿ(x)=x^(pⁿ)を証明した。
(p,φⁿ(d))=(p,d^(pⁿ))の実イデアル等式を証明し、完全係数δ環では実φⁿが誘導する
A/(p,d)≃A/(p,φⁿ(d))≃A/(p,d^(pⁿ))を既存商同型で構成した。
両商同型が標準代表元を実φⁿ係数像へ送ることも公開した。d正則性・distinguished性・完備性は仮定しない。
対象2704ジョブ成功、自分のコード警告なし。pure B4監査全2256宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は実prism冪剰余のG10判定を一般対象に適用し、この商同型へ接続する。
G9・実Frobenius段の平坦性・filtered colimit/完備化・候補CFF・一般B4は未完成として保持する。

## Frobeniusで動かした実還元への忠実平坦性移送計画（2026-10-16）

BS担当でPerfectDeltaPrismaticDerivedFlat.leanを新設する。
新しい係数商イデアル等式とprism冪剰余のG10判定を組み合わせ、
元の実(p,d)還元が次数零・H0忠実平坦なら実(p,φⁿ(d))還元もそうなることを証明する。
完全基底δ環では、実φⁿで誘導されたA/(p,d)→A/(p,φⁿ(d))係数作用への制限でもH0が忠実平坦となることを証明する。
既証の完全prism・有限根族の実逐次源を代入し、追加の還元・平坦性入力なしの具体的公開定理を付ける。
これは移動した係数剰余での結果であり、Frobeniusねじれ源との導来比較自体は後続工程として区別する。
ビルド・BS監査後に別コミットする。

## 一般実prism冪剰余へのG10・忠実性判定の適用結果（2026-10-16）

PrismaticPowerDerivedFlat.leanに2公開宣言を実装した。
任意の上有界実A対象Xについて、標準冪零商の実還元を元の実A/(a,d)還元の係数制限へ比較した。
元の実還元の非零次数消滅・H0忠実平坦性という明示入力から、共通G10で実A/(a,dⁿ)還元の次数零集中・H0平坦性を得た。
共通の正規化single/H0通常tensor比較と冪零作用による忠実性判定を再利用し、H0忠実平坦性も証明した。
a,dの正則性・Noether性・完備性・ねじれ上界は追加していない。n>0と入力還元の性質は明示している。
これはBSのprism冪剰余への既存共通APIの適用であり、G10・一般Tor/導来完備性の再定義ではない。
対象2870ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2258宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。次はa=p,n=p^kを用いて実Frobenius係数剰余へ接続する。
G9・実Frobeniusねじれ段との比較・filtered colimit/完備化・候補CFF・一般B4は未完成として保持する。

## 実Frobenius係数剰余への忠実平坦性移送の実装結果（2026-10-16）

PerfectDeltaPrismaticDerivedFlat.leanに3公開定理を実装した。
元の実(p,d)還元の次数消滅・H0忠実平坦性という明示入力から、G10のprism冪剰余判定と
(p,φⁿ(d))=(p,d^(pⁿ))のイデアル等式で、実(p,φⁿ(d))還元の次数零集中・H0忠実平坦性を証明した。
完全基底では、実φⁿが誘導する商係数同型に沿って元のA/(p,d)へ制限したH0も忠実平坦と証明した。
完全prism・有限根族の元の実逐次源へ適用し、具体的P・完全性・b・有限全列挙・反復数kだけから両入力を供給した。
これは移動した係数剰余に関する結果であり、実Frobeniusねじれ源そのものとの同一視は未証明として保持する。
対象3910ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2261宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。
次はMathlibのrestrictScalarsEquivalenceOfRingEquivと同値による射影対象保存を使い、
実φⁿ係数制限の射影モデルと、標準商の底変換との可換図式をBSの具体的φⁿへ構成する。
既存のboundedAboveDerivedRestrictScalarsModelIso・boundedAboveDerivedBaseChangeModelIsoを再利用する。
これにより今回の移動係数還元を実Frobeniusねじれ段へ接続し、δ完全化のfiltered colimitへ進む。
G9・元の源の環としての離散性・filtered colimit/完備化・候補CFF・一般B4は未完成として保持する。

## 実Frobeniusねじれ源の射影モデルと係数商square計画（2026-10-16）

BS担当でPerfectDeltaFrobeniusModels.leanを新設する。
Mathlibの環同値による係数制限の圏同値・射影対象保存を実φⁿへ適用し、
既存の上有界モデルを実φⁿ係数制限対象のモデルへ変換する。既存の実導来底変換モデル比較を再利用する。
次にPerfectDeltaFrobeniusQuotientSquare.leanを新設する。
共通restrictScalarsIsoExtendInverseとModuleCat.extendScalarsCompを使い、
φⁿ係数制限後の標準(p,d)商と、元対象の(p,φⁿ(d))商後の正確な商係数制限との通常関手squareを構成する。
同じsquareを射影モデル・既存derivedRestrictScalarsFactorsで実導来対象へ持ち上げ、元の同じ係数作用を保持する。
新たな一般底変換・Tor・射影モデル定義は作らず、共通基盤とMathlibを実φⁿへ適用する。
各段階のビルド・BS監査後に個別コミットする。G9・filtered colimit/完備化・候補CFF・一般B4は別工程。

## 実Frobeniusねじれ段の(p,d)還元判定計画（2026-10-16）

BS担当でPerfectDeltaFrobeniusStageFlat.leanを新設する。
実係数商squareと共通の係数制限ホモロジー比較を合成して、
φⁿで係数制限した実対象の標準(p,d)還元のホモロジーを、移動係数剰余の正確な係数制限へ同定する。
前段の移動剰余判定から、ねじれ段そのものの非零次数消滅・H0忠実平坦性を証明する。
完全prism・有限根族の元の実逐次源へ適用して追加の還元・平坦性仮定なしの具体的入力を公開する。
ビルド・BS監査後に別コミットし、δ環としての実段との線形比較・filtered colimitは後続工程とする。

## 実Frobenius係数制限の射影モデルの実装結果（2026-10-16）

PerfectDeltaFrobeniusModels.leanに3公開宣言を実装した。
Mathlibの環同値による係数制限の圏同値・射影対象保存を実φⁿへ適用し、射影加群の保存を証明した。
指定した既存上有界射影モデルを実φⁿ係数制限対象のモデルへ移し、その同じモデルでの実係数商還元比較を公開した。
既存のモデル・導来係数制限・底変換比較を再利用し、追加のTor/平坦性仮定や新モデルの一般定義を導入していない。
対象2705ジョブ成功、自分のコード警告なし。pure B4監査全2264宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は逆同型による係数拡大の既存自然同型で実係数商squareを構成する。
G9・ねじれ段の還元判定・filtered colimit/完備化・候補CFF・一般B4は未完成として保持する。

## 実Frobenius係数商squareの実装結果（2026-10-16）

PerfectDeltaFrobeniusQuotientSquare.leanに4公開宣言を実装した。
実逆Frobeniusと標準商射の代表元上の係数図式を証明し、共通restrictScalarsIsoExtendInverseと
ModuleCat.extendScalarsCompを合成して、φⁿ係数制限後の標準(p,d)拡大と
(p,φⁿ(d))拡大後の正確な商係数制限との通常関手自然同型を構成した。
このsquareを項ごとに適用し、移送した同じ射影モデルと既存導来比較を使って実導来squareへ持ち上げた。
二つのA作用を暗黙に一致させず、環同値・標準商写像・指定したモデルを明示している。
対象2921ジョブ成功、自分のコード警告なし。pure B4監査全2268宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は移動係数剰余の次数消滅とH0忠実平坦性を、実ねじれ段へ渡す。
G9・δ環としての各段との比較・filtered colimit/完備化・候補CFF・一般B4は未完成として保持する。

## 実Frobeniusねじれ対象の標準還元判定の実装結果（2026-10-16）

PerfectDeltaFrobeniusStageFlat.leanに4公開宣言を実装した。
実係数商squareと共通の係数制限ホモロジー比較を合成し、φⁿ係数制限対象の標準(p,d)還元のホモロジーを、
移動係数剰余の正確な商係数制限へ同定した。
元対象の標準(p,d)還元の非零次数消滅・H0忠実平坦性という明示入力から、
実ねじれ対象の標準還元にも非零次数消滅とH0忠実平坦性が成り立つと証明した。
完全prism・有限根族の元の実逐次源へ適用し、具体的P・完全性・b・有限全列挙・反復数だけから入力を供給した。
対象3913ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査全2272宣言成功。
標準3公理以外なし、新sorry・公理・外部引用なし。
次はδ環射j : (A,D)→(B,E)について、実係数射j_n=φ_Bⁿ∘jとj∘φ_Aⁿをδ自然性で照合する。
既存baseChangeScalarModule j_nを使い、実φ_Aⁿ制限加群との恒等線形同型・single比較を構成して今回の判定へ渡す。
新たな同等の一般加群定義は作らず、実δ完全化の環段へ接続する。その後、実段図式とδ完全化のfiltered colimitを照合する。
G9・元の源の環としての離散性・filtered colimit/完備化・候補CFF・一般B4は未完成として保持する。

## 実δ環のFrobenius各段の係数作用と線形比較計画（2026-10-16）

BS担当でDeltaAlgebraFrobeniusStages.leanを新設する。
δ環射j : (A,D)→(B,E)と実係数射j_n=φ_Bⁿ∘jを用い、δ自然性でj_n=j∘φ_Aⁿを照合する。
既存baseChangeScalarModule j_nを各実環段のA加群として使い、実φ_Aⁿ制限加群との恒等線形同型、
既存の係数制限single比較による実次数零対象の比較を構成する。
実φ_BによるA線形隣接遷移と、その具体的逐次ModuleCat図式も公開する。
次にDeltaAlgebraFrobeniusStageFlat.leanを新設し、元の実Bの(p,d)還元が次数零・H0忠実平坦である入力から、
全実環段B（正確なj_n作用）の標準還元の非零次数消滅・H0忠実平坦性を証明する。
既存の加群定義・一般導来底変換・Frobeniusねじれ判定を再利用し、G9や環としての源の離散性は仮定に隠さない。
各段階をビルド・BS監査後に個別コミットする。実δ完全化とのcolimit比較は次工程。

## 実δ完全化への正確なA線形標準余錐計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionCocone.leanを新設する。
既存DeltaPerfection Eと第0段の係数射jの合成を実完全化のA係数射とし、既存δ自然性でδ環射であることを証明する。
各実段のj_n作用から標準deltaPerfectionOf E nへのA線形性を係数図式で証明する。
隣接Frobenius遷移との可換性を示し、前段の具体的ModuleCat逐次図式から実δ完全化加群への標準余錐を構成する。
加群・環の余極限を再定義せず、既存環余極限の値と係数作用を保持する。
余錐の普遍性と実δ完全化の還元判定は次工程として区別し、対象ビルド・BS監査後に個別コミットする。

## 実δ環のFrobenius各段の係数加群の実装結果（2026-10-16）

DeltaAlgebraFrobeniusStages.leanに7公開宣言を実装した。
実係数射j_n=φ_Bⁿ∘jを定め、δ環射jの自然性からj_n=j∘φ_Aⁿを証明した。
既存baseChangeScalarModule j_nを各実環段の正確なA加群として使い、実基底Frobenius制限加群との恒等線形同型とsingle比較を構成した。
隣接する実φ_BのA線形遷移、およびその具体的逐次ModuleCat図式と標準隣接射を公開した。
新たな同等の加群・環段の定義は作らず、別々の係数作用を束ねた既存加群を使用する。
対象2608ジョブ成功、自分のコード警告なし。pure B4監査全2279宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は既証の実ねじれ判定をこの同じ実環段の還元へ渡す。
G9・源の離散性・実δ完全化とのcolimit比較・候補CFF・一般B4は未完成として保持する。

実δ完全化余錐工程の拡張（2026-10-16）：MathlibのModuleCatのfiltered colimit反映と
Types.FilteredColimit.isColimitOf'が既存で利用可能なことを確認した。
別のModule.DirectLimitを定義せず、環余極限の代表元・zero_exactで標準余錐の普遍性まで同工程で証明する。
任意二段の実図式射の値をFrobenius反復へ照合し、標準段射を保つ圏論的colimit同型も公開する。

## 実δ環各段の標準還元判定の実装結果（2026-10-16）

DeltaAlgebraFrobeniusStageFlat.leanに3公開定理を実装した。
完全な係数δ環D、δ環射j、元の実Bの標準(p,d)導来還元の非零次数消滅・H0忠実平坦性から、
正確なj_n作用を持つ全実環段の同じ還元の非零次数消滅・H0忠実平坦性を証明した。
通常の標準剰余テンソルの忠実平坦性も、既存の実H0比較で導いた。
G10はPrismaticPowerDerivedFlatを経由して使用しており、源の離散性を暗黙に仮定しない。
対象3921ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2282宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。G9全体・源の環としての離散性・完全化の還元・候補CFF・一般B4は未完成。

## 実δ完全化へのG7接続計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionTor.leanを新設する。
実δ完全化の正確なA加群colimit同型を共通G7のtorAlg_colimit_isZero_of_stagesへ渡す。
完全係数δ環D・δ環射jと元Bの標準(p,d)還元の非零次数消滅・H0忠実平坦性から、
各実段の既証消滅を使い、実DeltaPerfection Eの正のTorAlgと負次数還元ホモロジーの消滅を証明する。
一般のTor/ホモロジー比較は追加せず、既存導来比較をこの具体的係数射へ適用する。
忠実平坦性・導来完備化後の判定は別工程とし、対象ビルド・BS監査後に個別コミットする。

## 実δ完全化の正確な加群余極限の実装結果（2026-10-16）

DeltaAlgebraPerfectionCocone.leanに11公開宣言を実装した。
実係数射・そのδ自然性、各実段から既存環完全化へのA線形標準射と余錐を構成した。
任意二段の図式射を実Frobenius反復へ同定し、既存環余極限の代表元と零判定から標準余錐の普遍性を証明した。
Mathlibのfiltered colimit保存を小さい添字宇宙へ制限し、同型反映から加群colimitを反映した。
圏論的加群colimitと既存DeltaPerfection Eとの同型および全標準段射の可換性を公開した。
別の加群・環余極限は再定義していない。対象2617ジョブ成功、警告なし。pure B4監査2293宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次はこの同じ図式にG7を適用する。完全化後の還元・候補CFF・一般B4は未完成。

## 実δ完全化へのG7接続の実装結果（2026-10-16）

DeltaAlgebraPerfectionTor.leanに2公開定理を実装した。
完全係数δ環D・δ環射jおよび元の実Bの標準(p,d)還元の非零次数消滅・H0忠実平坦性から、
共通G7と実δ完全化の正確な加群colimit同型を使い、実DeltaPerfection Eの正のTorAlg消滅を証明した。
既存の同じ実導来底変換とホモロジー比較で、同じ還元の全負次数ホモロジー消滅も得た。
対象3926ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2295宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。元のBの還元入力を明示した証明済み定理であり、候補の無条件CFFとは区別する。
次は実δ完全化の標準剰余の平坦性・単位に基づく忠実性と、導来完備化後の比較。
G9全体、源の環としての離散性、候補CFF、引用なしの一般B4は未完成。

## 実δ完全化の標準剰余の通常平坦性計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionResidueFlat.leanを新設する。
前段の正確な加群colimit同型に既存係数拡大関手のcolimit保存を適用し、
実標準剰余テンソルを各実段の標準剰余テンソルのcolimitへ同定する。
共通G7の通常Torの逐次colimit保存・既存Tor対称性・Tor一次からのテンソル単射判定を使い、
各段の既証平坦性から同じ実剰余テンソルの平坦性を証明する。
同等の一般colimit平坦性定義や補題を新設せず、このBS具体図式へ既存APIを適用する。
忠実性は単位を使う後続工程として区別し、ビルド・専用監査後に個別コミットする。

## 実δ完全化の標準剰余の忠実性計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionResidueFaithful.leanを新設する。
各実環段の標準剰余テンソル内の1⊗1を明示し、各段の忠実平坦性による単位テンソル写像の単射性を証明する。
実Frobenius遷移がその単位を保存することを確認し、通常テンソル関手のcolimit保存とfiltered colimitの等式検出を使って
実δ完全化の同じ標準剰余テンソルの忠実性へ渡す。一般の忠実平坦加群の余極限が忠実平坦とは仮定しない。
前段の通常平坦性と合わせる入口とH0への既存比較を公開する。対象ビルド・専用監査後に個別コミットする。

## 実δ完全化の標準剰余の通常平坦性の実装結果（2026-10-16）

DeltaAlgebraPerfectionResidueFlat.leanに2公開宣言を実装した。
実標準剰余テンソルと実段の剰余テンソルの加群colimitとの同型を、既存係数拡大のcolimit保存から構成した。
共通G7による通常Torの逐次colimit保存・既存Tor対称性・一次Torからの単射判定を使い、
完全係数δ環・δ環射・元Bの標準還元入力から同じ実δ完全化の標準剰余テンソルの通常平坦性を証明した。
対象3927ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2297宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。忠実性は環単位を明示して次工程で証明する。
導来完備化比較・源の離散性・候補CFF・一般B4は未完成。

## 実δ完全化の標準還元と標準augmentationの比較計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionResidue.leanを新設する。
既存の負ホモロジー・Tor判定を実δ完全化へ適用し、実標準係数射のscalarExtensionTorVanishingを供給する。
既存boundedAboveDerivedBaseChangeModuleAugmentationIsoを使い、同じ標準augmentationによる実導来還元と
実通常剰余テンソルのsingleとの同型を構成し、全非零次数消滅を公開する。
前段H0忠実平坦性と合わせて完全な還元入力を後続の完備化比較へ渡す。
任意の同型を選んで標準射の問題を隠さず、既存標準augmentationを再利用する。各ビルド・監査後に別コミットする。

## 実δ完全化の標準剰余の忠実性の実装結果（2026-10-16）

DeltaAlgebraPerfectionResidueFaithful.leanに6公開宣言を実装した。
各実環段の剰余内の1⊗1と全遷移での保存、および各段の単位テンソル単射性を証明した。
通常テンソルのcolimit保存と、忘却後のfiltered colimitの同段等式検出により、
実δ完全化の標準剰余テンソルの忠実平坦性を証明した。任意の忠実平坦加群図式の余極限には一般化していない。
既存の同じ実H0比較により、同じ実導来還元のH0忠実平坦性も公開した。
対象3928ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2303宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。完全係数δ環・δ環射・元Bの還元入力を明示する。
次は標準augmentationによる実還元全体の次数零比較。源の離散性・完備化比較・候補CFF・一般B4は未完成。

## 実δ完全化の標準還元全体の比較の実装結果（2026-10-16）

DeltaAlgebraPerfectionResidue.leanに3公開宣言を実装した。
実δ完全化の同じ標準係数射に対してscalarExtensionTorVanishingを供給し、
既存標準augmentationによる実導来還元と実通常剰余テンソルのsingleとの同型を構成した。
これにより全非零次数ホモロジー消滅を公開し、前段のH0忠実平坦性と合わせた還元入力が揃った。
仮定は完全係数δ環・δ環射・元の実Bの標準還元の次数消滅とH0忠実平坦性のままである。
対象3929ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2306宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は同じ実δ完全化singleの逐次p,d導来完備化へ既存の標準単位比較を適用する。
源の離散性・完備化H0候補との標準射比較・候補CFF・一般B4は未完成。

## 実δ完全化の逐次導来完備化への標準還元接続計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionCompletionResidue.leanを新設する。
既存実δ完全化の正確なA加群singleに、既存のp方向・d方向の実導来完備化関手を逐次適用する。
係数環Aのp,dの個別正則性の下、既存prismaticCoefficientIteratedCompletionPairIsoを適用し、
同じ実(p,d)還元と未完備の実δ完全化還元を標準単位の図式とともに比較する。
完全係数δ環の場合p正則性はその完全性から供給し、前段の還元入力から逐次完備化後の
全非零次数ホモロジー消滅・H0忠実平坦性を証明する。d正則性は明示し、完全prismへ適用可能な型とする。
H0環候補との同一視や源の離散性をここで仮定しない。ビルド・BS専用監査後に別コミットする。

## 実δ完全化の逐次導来完備化とG8の接続計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionCompletionRestriction.leanを新設する。
実δ完全化C=DeltaPerfection E、元の係数射κ:A→Cを保持し、既存single係数制限比較と
共通G8のboundedAboveCompletionRestrictionIsoをp,dの二方向に適用する。
A上の実逐次完備化と、C上でκ(p),κ(d)の実逐次完備化をしてAへ制限した対象の同型を構成する。
元の二つの標準単位の合成を保つ図式と、同じ実H0の係数制限比較を公開する。
この対象をPDCompletionH0環候補のsingleと自動同一視せず、その比較・離散性は後続工程。ビルド・監査後に別コミットする。

## 実δ完全化の逐次完備化後の還元入力の実装結果（2026-10-16）

DeltaAlgebraPerfectionCompletionResidue.leanに5公開宣言を実装した。
同じ実δ完全化singleへの実p,d逐次導来完備化を用い、元の両標準単位の合成を保つ還元同型を構成した。
完全係数δ環のp正則性と明示したd正則性の下、元Bの還元入力から、
同じ実逐次完備化後の標準還元の全非零次数消滅・H0忠実平坦性を証明した。
対象3930ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2311宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。完備化H0環候補との同一視・源の離散性・候補CFF・一般B4は未完成。
次はG8により同じ対象を実δ完全化環上の逐次完備化の係数制限へ比較する。

## 完全prism上の実δ完全化逐次対象の完備入力計画（2026-10-16）

BS担当でPerfectPrismDeltaAlgebraCompletionInputs.leanを新設する。
同じ実δ完全化singleの逐次対象について、共通のKoszul段・ホモトピー逆極限の完備性からp完備性を証明し、
最後のd完備化によるd完備性を公開する。一般の完備化保存APIを重複定義せず、既存の共通定理をこの具体対象へ適用する。
完全oriented prism Pとδ環射jに対し、Pの生成元正則性と前段の実還元比較を用い、
同じ逐次対象のp,d導来完備性・標準還元全非零次数消滅・H0忠実平坦性を束ねた公開入力を供給する。
元Bの還元条件は明示し、候補CFFや源の環としての離散性とは区別する。ビルド・監査後に個別コミットする。

## 実δ完全化の逐次完備化へのG8接続の実装結果（2026-10-16）

DeltaAlgebraPerfectionCompletionRestriction.leanに4公開宣言を実装した。
元の実δ完全化Cとκ:A→Cについて、singleの正確な係数制限比較と、
A上の実p,d逐次完備化とC上の実κ(p),κ(d)逐次完備化のA係数制限との同型を構成した。
共通G8の元の両標準単位を保つ図式を合成し、同じ実H0の係数制限比較も公開した。
追加の正則性・平坦性・完備性を仮定せず、既存の実関手・標準単位を再利用する。
対象3940ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2315宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。C上の実逐次対象をH0環候補のsingleと自動同一視しない。
源の離散性・候補H0との標準射比較・候補CFF・一般B4は未完成。

## 完全prism上の実δ完全化逐次対象の完備入力の実装結果（2026-10-16）

PerfectPrismDeltaAlgebraCompletionInputs.leanに3公開定理を実装した。
同じ実逐次対象のp導来完備性を、共通のKoszul段・mapping cone・ホモトピー逆極限の完備性から証明し、
最後のd完備化によるd導来完備性も公開した。
完全oriented prism Pとδ環射j、元Bの明示した標準還元条件から、
同じ具体的逐次対象のp,d導来完備性・標準還元全非零次数消滅・H0忠実平坦性を同時に供給した。
生成元の正則性はP.generator_regularから供給し、追加の源の離散性や候補CFFは入力に隠していない。
対象3931ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2318宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は同じ実逐次対象の生成元冪商にG10とG8を適用し、G9用の正確な商上入力へ渡す。
元の源の環としての離散性、完備化H0候補との標準射比較、候補CFF、引用なしの一般B4は未完成。

## 実δ完全化逐次対象の生成元冪商とG9入力計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionPowerComplete.leanを新設する。
同じ実逐次対象のA/(dⁿ)への実還元を既存の正則主元Koszul比較によりdⁿ錐へ同定し、
p導来完備性をmapping coneへ移す。共通G8の標準単位と係数制限の同型反映により、
その同じ対象のA/(dⁿ)上でのp導来完備性を証明する。n=0も含め、生成元正則性は明示する。
次にPerfectPrismDeltaAlgebraPowerInputs.leanを新設する。完全prism上で前段の標準(p,d)還元入力を
既存G10のprismaticPowerDerivedReduction_pure_faithfullyFlatへ渡し、実A/(p,dⁿ)還元の純粋性・平坦性を得る。
既存の標準mod p二段商比較と共通G8を用い、同じA/(dⁿ)上の対象についてp完備性・係数のpⁿねじれ上界・
標準mod p還元の全非零次数消滅・H0平坦性を束ねる。G9-4の選択モデルの余核比較にも接続する。
元Bの標準還元条件は明示し、G9全体や源の離散性を完成とはしない。各ビルド・BS監査後に個別コミットする。

## 実δ完全化逐次対象の生成元冪商完備性の実装結果（2026-10-16）

DeltaAlgebraPerfectionPowerComplete.leanに2公開宣言を実装した。
元の正確な実逐次対象のA/(dⁿ)への実還元を、係数制限後の同じdⁿ Koszul錐へ比較した。
既存のp完備性をmapping coneへ移し、共通G8の標準単位と係数制限の同型反映で
その同じ還元対象がA/(dⁿ)自身の上でp導来完備であることを証明した。n=0も含む。
対象3941ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2320宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。dの正則性は明示し、源の離散性や候補CFFは仮定しない。
次は完全prismに特化し、G10と標準mod p商比較、係数のpⁿねじれ上界を同じ対象に供給する。一般B4は未完成。

## 実δ完全化逐次対象の生成元冪商のG9入力の実装結果（2026-10-16）

PerfectPrismDeltaAlgebraPowerInputs.leanに3公開定理を実装した。
完全prism P・δ環射j・元Bの明示した標準還元入力から、G10を同じ実逐次対象に適用し、
実A/(p,dⁿ)還元の次数零性とH0平坦性を得た。標準二段商比較で、
同じ実A/(dⁿ)対象の標準mod p還元の全非零次数消滅とH0平坦性へ移した。
共通G8の商環上のp完備性と、完全prismの既存pⁿねじれ上界を同じ対象に束ねたG9入力を公開した。
共通G9-4の比較にも適用し、同じ対象の選択射影モデルのp余核複体の次数消滅を証明した。
対象3953ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2323宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。元Bの還元条件を候補の無条件CFFと同一視していない。
元の有限根族源と実δ完全化逐次対象の双方についてG9の正確な入力は供給済みであり、
共通正本のG9全体は現在も未完成。最終離散性・H0ねじれ評価の適用、実H0環候補との標準射比較、
無限根族と候補CFF、引用なしの一般B4は残る。

## G9と独立した直接PD完備化と既存p先行候補の環比較計画（2026-10-16）

BS担当でDeltaPerfectionPDCompletionUniversal.leanを新設する。既存DeltaPerfection EとPCompletedDeltaPerfection Eをそのまま使い、
それぞれの実PDCompletionH0から、完全δ試験環Tへのδ射の一意延長を証明する。
試験環のp・元の元bの像に関する実導来完備性を明示し、前者はδ完全化普遍性と実PD完備化普遍性、
後者は既存p完備δ完全化普遍性と実PD完備化普遍性を合成する。完全性からp正則性を得て、必要な古典的p完備性の比較を証明する。
次にDeltaPerfectionPDCompletionComparison.leanを新設し、同じ両普遍性から具体的な双方向環射と標準raw射を保つ環同型を構成する。
既存候補のp先行手順を直接PD完備化へ比較する工程であり、未完全化の源を完全候補と同型とする工程ではない。
新しい環・完備化や同等の一般一意性定義は作らず、既存の実環・δ構造・標準射を再利用する。各ビルド・監査後に個別コミットする。
G9による源の離散性と、実導来対象のH0との比較・候補CFF・一般B4は別工程として残す。

## 直接PD完備化とp先行候補の共通普遍性の実装結果（2026-10-16）

DeltaPerfectionPDCompletionUniversal.leanに2公開定理を実装した。
既存DeltaPerfection Eを直接実PD完備化したH0と、既存PCompletedDeltaPerfection Eを実PD完備化したH0について、
完全δ試験環Tへの、元Bからのδ射を保つ一意延長を証明した。
Tのp,f(b)に関する実導来完備性を明示し、p先行側で必要な古典的p完備性は、完全性によるp正則性と既存比較から供給した。
既存δ完全化・p完備δ完全化・実PD完備化の普遍性を合成し、新たな完備化や環の定義は作っていない。
対象2891ジョブ成功、警告なし。pure B4監査2325宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は両普遍性から具体的な双方向δ射と標準raw射を保つ環同型を構成する。
源の離散性・実導来対象とのH0比較・候補CFF・一般B4は未完成。

## 既存根添加候補への直接PD完備化比較の具体化計画（2026-10-16）

BS担当でDeltaRootDirectPDCompletionComparison.leanを新設する。前段の標準環同型を既存の根添加raw δ環へ適用し、
そのδ完全化の直接実PD完備化H0と既存DeltaRootPrismCarrierとの具体的環同型を構成する。
元raw環・元Aからの標準係数射・選択生成元の像を保つことを証明し、distinguished条件の下で
標準主イデアル商の環同型と既存perfectoid候補への係数射の整合へ降ろす。
任意の根族を扱い有限性やG9、源の離散性、平坦性は仮定しない。新たな候補環の同等定義は作らず既存PDCompletionH0を使用する。
この環比較を導来対象のsingle同型や候補CFFと同一視しない。ビルド・BS専用監査後に別コミットする。

## 直接PD完備化と既存p先行候補の標準環同型の実装結果（2026-10-16）

DeltaPerfectionPDCompletionComparison.leanに6公開宣言を実装した。
前段の同じ試験環への普遍性から具体的な双方向δ射を構成し、両合成が恒等射であることを一意性で証明した。
既存DeltaPerfection Eの直接実PD完備化H0と、PCompletedDeltaPerfection Eの実PD完備化H0との環同型、
両方向のδ両立性、元Bからの両標準raw射との可換性を公開した。任意のE,bを扱い、distinguished・平坦性・源の離散性は仮定しない。
対象2893ジョブ成功、警告なし。pure B4監査2331宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は同じ同型を既存根添加候補へ具体化し、係数射と標準商へ降ろす。
実導来対象のH0との比較・源の離散性・候補CFF・一般B4は未完成。

## 既存根添加候補への直接PD完備化比較の実装結果（2026-10-16）

DeltaRootDirectPDCompletionComparison.leanに8公開宣言を実装した。
既存根添加raw δ環のδ完全化を直接実PD完備化したH0と、既存DeltaRootPrismCarrierとの具体的環同型を構成した。
元raw環・元Aの標準係数射・選択生成元の像を保つことを証明し、distinguished条件の下で標準主イデアル商へ降ろした。
既存DeltaRootPerfectoidCandidateとの商環同型、代表元上の公式、具体的係数射との整合を公開した。
既存perfectoid性をこの同じ商環同型で運び、直接PD完備化側の具体的商の整perfectoid性も証明した。
任意の根族を扱い、有限性・源の離散性・平坦性・G9を仮定しない。新たな候補環の同等定義は作っていない。
対象3771ジョブ成功、警告なし。pure B4監査2339宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。これにより候補の直接PD・p先行PDという完備化手順の違いは標準係数射と商を保って解消した。
残る比較は、元の実導来源の離散化・δ環構造と、その実δ完全化逐次導来対象のH0をこの直接PD完備化H0環へ接続する工程。
共通G9全体は現コード・共通監査・正本で依然未完成。候補CFF・無限根族の全射性への合流・引用なし一般B4は未完成。

## 実δ完全化逐次対象から直接PD完備化H0への標準射計画（2026-10-16）

BS担当でDeltaAlgebraPerfectionPDCompletionMap.leanを新設する。
C=DeltaPerfection E、κ:A→Cに対し、既存PDCompletionH0 C p (κ d)を、標準射s∘κの正確なA作用で使用する。
既存の自己作用・係数制限の完備性をこのsame singleへ接続し、標準C→H0をA線形射・実single射へ移す。
共通の実導来完備化反射により、この標準射を同じ実p,d逐次対象からの一意延長へ構成し、
両標準単位の合成を保つ図式と、具体的対象・係数写像を固定した一意性を公開する。
新しい完備化・候補環や一般反射定義を作らず、既存実対象とPDCompletionH0を使う。
この射の同型性・源の離散性・H0環比較の完成は主張しない。ビルド・BS専用監査後に個別コミットする。

## 元の実根添加源と完全化候補への標準三角図式計画（2026-10-16）

BS担当でDeltaRootSourcePerfectionCandidate.leanを新設する。既存の元の実導來源からraw singleへの標準augmentationを使い、
raw δ完全化の正確なA作用付きsingleへの標準射を構成する。前段の直接PD完備化へのsingle射と、
既証の直接PD・既存根候補の環同型をA線形射へ移したものを合成し、元の既存deltaRootSourceCandidateMapへ一致する三角図式を証明する。
元A作用と元raw射を明示し、新たな源・候補環は定義しない。G9・源の離散性・平坦性は仮定しない。
その後、同じ三角図式を元の両実完備化単位の自然性・一意延長により逐次導来完備化後へ移す。
各ビルド・BS監査後に個別コミットする。同型性や候補CFFはこの標準図式だけから推論しない。

## 実δ完全化逐次対象から直接PD完備化H0への標準射の実装結果（2026-10-16）

DeltaAlgebraPerfectionPDCompletionMap.leanに9公開宣言を実装した。
C=DeltaPerfection E、κ:A→C、s:C→PDCompletionH0 C p (κ d)の元の標準射を、
正確なs∘κ作用でA線形射と実single射にした。終域の同じsingleのp,d導来完備性を既存の自己作用との比較で証明した。
共通の実完備化反射で、同じ実p,d逐次対象からの標準延長を構成し、元の両単位の合成上の図式と一意性を公開した。
追加の正則性・平坦性・源の離散性を仮定せず、新たな完備化・候補環・一般反射は定義していない。
対象3976ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2348宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。この射の同型性は未証明であり、実H0比較の完成とは数えない。
次は元の根添加実源と既存候補の標準三角図式へ接続する。源の離散性・候補CFF・一般B4は未完成。

実源の標準三角図式の逐次完備化工程（2026-10-16）：BS担当でDeltaRootSourcePerfectionCandidateCompletion.leanを新設する。
元の既存実二因子源からδ完全化singleへの標準射に両既存実完備化関手を適用し、その合成標準単位の自然性を証明する。
前段の直接PD完備化H0への標準一意延長と既存根候補へのsingle比較を合成すると、
既存deltaRootSourceCandidateIteratedMapに一致することを、元の両標準単位上の図式と既存の一意性から証明する。
新たな源・候補・完備化定義や同型性仮定は導入しない。ビルド・監査後に別コミットする。

## 元の実根添加源と完全候補への標準三角図式の実装結果（2026-10-16）

DeltaRootSourcePerfectionCandidate.leanに5公開宣言を実装した。
元の既存実二因子源からraw singleへの既存augmentationを経由し、raw δ完全化の正確なA作用付きsingleへの標準射を構成した。
直接PD・既存根候補の環同型を元Aの正確な係数作用について線形化し、single射へ移した。
δ完全化・直接PD標準射・既存候補比較を通る射が、元のdeltaRootSourceCandidateMapそのものに一致する三角図式を証明した。
元Aの係数射はraw標準射とMvPolynomial.Cの合成を明示し、生成元の像も同じ既存環構造で使用する。
任意の根族を扱い、有限性・G9・源の離散性・平坦性は仮定しない。
対象4152ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2353宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は同じ三角図式を両実完備化単位の自然性と既存一意延長で逐次完備化後へ移す。
この図式を同型性や候補CFFと同一視しない。G9本体・源の離散性・実H0同型・一般B4は未完成。

## 元の実源と完全候補の標準三角図式の逐次完備化結果（2026-10-16）

DeltaRootSourcePerfectionCandidateCompletion.leanに3公開宣言を実装した。
元の実源からδ完全化singleへの同じ標準射へ両既存完備化関手を適用し、元の両合成標準単位の自然性を証明した。
δ完全化逐次対象から直接PD完備化H0への既存標準一意延長と、既存根候補へのsingle比較を合成すると、
元のdeltaRootSourceCandidateIteratedMapそのものに一致することを、両標準単位上の図式と既存の一意性から証明した。
任意根族を扱い、G9・源の離散性・平坦性・同型性を仮定していない。新たな源・候補・完備化は定義しない。
対象4154ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2356宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。標準射の一致を同型性や候補CFFの完成とは数えない。
共通G9全体は現在も未完成。元の実源の離散化・δ環構造との比較、実δ完全化逐次対象のH0同型、候補CFF・一般B4は残る。

## PD完備化をδ完全化の前へ挟む手順との標準環比較計画（2026-10-16）

BS担当でDeltaPDCompletionPerfectionUniversal.leanを新設する。元のδ環(B,E)とbについて、
既存PDCompletionH0 B p bの既存δ構造をδ完全化し、その後に同じ生成元の像で実PD完備化したH0を扱う。
完全δ試験環Tのp,f(b)実導来完備性を明示し、同じ元Bのδ射を保つ一意延長を、既存PD完備化普遍性と
δ完全化後PD完備化の既証普遍性から合成する。
次にDeltaPDCompletionPerfectionComparison.leanを新設し、未完備Bのδ完全化を直接PD完備化したH0との
具体的な双方向δ射・標準元B射を保つ環同型を両普遍性から構成する。
これは二つの既存H0環構成の比較であり、元の実二因子導来源の離散性・δ構造や実H0との同型は仮定も結論もしない。
新しい完備化・環・同等の一般一意性定義は作らない。各ビルド・BS専用監査後に個別コミットする。
G9による離散化・候補CFF・引用なし一般B4は別工程として残す。

PD先行δ完全化比較工程の拡張（2026-10-16）：同じ元bの両標準像の一致から、両標準主イデアル商の環同型、
代表元公式、元Bからの両標準係数射との図式まで同工程で証明する。商のperfectoid性や平坦性はここでは結論しない。

## PD完備化をδ完全化前へ挟む構成の普遍性の実装結果（2026-10-16）

DeltaPDCompletionPerfectionUniversal.leanに1公開定理を実装した。
元のδ環(B,E)の実PDCompletionH0を既存δ構造のままδ完全化し、同じ生成元像で再び実PD完備化したH0から、
完全δ試験環Tへの元B射を保つ一意延長を証明した。Tのp,f(b)実導来完備性を明示する。
既存の実PD完備化普遍性と既証δ完全化後PD完備化普遍性を合成し、新たな環・完備化・一般一意性は定義しない。
対象2892ジョブ成功、警告なし。pure B4監査2357宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は同じ元B射を保つ双方向δ射・環同型・標準主イデアル商比較を構成する。
この結果を元の実二因子源の離散性・δ構造・H0同型・候補CFF・一般B4の完成とは数えない。

## PD完備化をδ完全化前へ挟む手順との標準環・商比較の実装結果（2026-10-16）

DeltaPDCompletionPerfectionComparison.leanに10公開宣言を実装した。
元のδ環のδ完全化を直接PD完備化したH0と、元の実PDCompletionH0をδ完全化して再度PD完備化したH0の間に、
具体的な双方向標準δ射を構成し、両普遍性の一意性で合成が恒等射となることを証明した。
両方向のδ両立性、元Bの標準射との可換性、元bの両標準像の一致を公開した。
その生成元の標準主イデアル商についても環同型・代表元公式・元Bからの両標準係数射の可換性を証明した。
任意のE,bを扱い、正則性・distinguished・平坦性・源の離散性を仮定しない。新たな環・完備化は定義しない。
対象2894ジョブ成功、警告なし。pure B4監査2367宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。PD完備化をδ完全化の前へ挟む環構成の差は、標準元B射と生成元商を保って解消した。
元の実二因子導来源の完備化H0をこの既存PDCompletionH0環へ同一視したものではない。
共通G9全体・元の実源の離散化とδ構造・実H0との標準同型・候補CFF・引用なし一般B4は引き続き未完成。

## PD完備化済み根δ環からの構成と既存候補の比較計画（2026-10-16）

BS担当でDeltaRootPDCompletedPerfectionComparison.leanを新設する。既存根raw δ環の実PDCompletionH0と既存δ構造を用い、
そのδ完全化を同じ生成元像で実PD完備化したH0を、前段の順序比較と既存直接PD比較の合成で
DeltaRootPrismCarrierへ同定する。元raw環・元Aの標準射、生成元像、distinguished条件下の標準商と
既存perfectoid候補の係数射を保つことを証明する。商同型からこの構成側の整perfectoid性も供給する。
任意根族を扱い、有限性・G9・源の離散性・平坦性を仮定しない。新たな根候補や完備化は定義しない。
元の実二因子源のH0とこのPDCompletionH0との比較を済ませたとは扱わない。ビルド・BS専用監査後に個別コミットする。

## PD完備化済み根δ環から出発する既存候補比較の実装結果（2026-10-16）

DeltaRootPDCompletedPerfectionComparison.leanに8公開宣言を実装した。
既存根raw δ環の実PDCompletionH0を既存δ構造でδ完全化し、同じ生成元像で実PD完備化したH0を、
前段の順序比較の逆と既存直接PD比較の合成によりDeltaRootPrismCarrierへ標準環同型で接続した。
元raw環・元Aの標準射、生成元像を保ち、distinguished条件の下で標準主イデアル商・代表元・
既存perfectoid候補への係数射が整合することを証明した。商同型でこの構成側の整perfectoid性も供給した。
任意根族を扱い、有限性・G9・源の離散性・平坦性を仮定しない。新たな候補・完備化の同等定義は作っていない。
対象3774ジョブ成功、警告なし。pure B4監査2375宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。PD完備化済みδ環から出発する構成でも既存候補の係数射・生成元商が同じであることが確定した。
未解決の実源比較は、元の実二因子導来源を逐次導来完備化したH0をこのraw環のPDCompletionH0と同定し、
そのδ構造・標準射を照合する工程である。今回の環同型をその離散化・比較の証明としては扱わない。
共通G9全体は現ソース・共通正本・監査でなお未完成。候補CFF・引用なし一般B4は引き続き未完成。

## 共通基盤への要求 G11：実主元導来完備化の非正性保存とH0比較（2026-10-16、送信済み）

対象：任意可換環R、a:R、既存X,Y:DerivedCategory.Minus (ModuleCat.{u} R)。
要求1：X.obj.IsLE 0から、((boundedAboveDerivedCompletionFunctor R a).obj X).obj.IsLE 0。
可能なら任意k:ℤでIsLE kを同じkのまま保つ入口も供給する。正則性・Noether性・ねじれ有界性・完備性の追加仮定はしない。
要求2：X.obj.IsLE 0、Y.obj.IsLE 0、f:X⟶Y、IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom)から、
IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
  (((boundedAboveDerivedCompletionFunctor R a).map f).hom))。
関手・射・ホモロジーはいずれも既存の実対象を用いる。要求2を要求1と既存t構造・三角関手APIから導く場合も、元fそのものを保つ形を希望する。
利用工程：B4の元の実二因子根添加源からraw singleへの標準augmentationのH0同型を、p,dの逐次導来完備化後へ運ぶ。
これにより元の実源の完備化H0とraw環の同じ実完備化H0との比較へ進む。G9による負次数消滅・δ構造照合とは区別する。
既存API不足：BoundedAboveCompletion.leanのcomplexCompletion_isStrictlyLEとderivedComplexCompletionFunctor_isBoundedAboveは
上界をb+1とするだけで、H0比較に必要な同じ上界での非正性保存を与えない。既存DerivedTensorNonpositiveは源の入力を供給する。
本要求は主元Koszul塔の最上位ホモロジーの全射遷移とMilnor列の一般論であり、共通担当の範囲。BS内に同等の一般補題を重複実装しない。
待つ工程：標準augmentationのH0同型を実p,d完備化後へ運ぶ段階。G9の一般離散性判定もなお別途必要。
独立作業：DeltaRootSourceNonpositive.leanをBS担当で新設し、元Aへ制限した実源の正次数消滅・非正性、
および同じ実係数制限augmentationのH0同型を既存共通APIから証明する。新たな源・完備化・一般t構造定義は作らない。
2026-10-16、ユーザーの個別許可を得てG11をCLMSTへ送信済み。各ビルド・BS専用監査後に独立部分を個別コミットする。

## 元の実根添加源の非正性と標準augmentationのH0入力の実装結果（2026-10-16）

DeltaRootSourceNonpositive.leanに4公開定理を実装した。
元の二つの係数作用を保持した既存射影分解モデルのテンソルを用い、その項ごとの非正性を
元Aへの実係数制限後も保持することで、元の実源の非正性と全正次数ホモロジー消滅を証明した。
同じ標準augmentationの終域である係数制限raw singleの非正性も、既存single比較で証明した。
元のL上での標準augmentationのH0同型と、同じ実係数制限ホモロジー自然同型の図式から、
元A上のdeltaRootSourceRawCoefficientAugmentationそのもののH0同型を証明した。
任意根族・任意dを扱い、正則性・有限性・完備性・平坦性・源の離散性は仮定しない。
対象3856ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2379宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。G11の具体的X,Y,fについて両対象の非正性と元fのH0同型が揃った。
G11を共通基盤への要求として記録し、元のご指定に従い送信許可を非同期に確認中。現在は未送信。
G11によるp,d逐次完備化後のH0比較と、G9による源の離散化・δ構造照合、候補CFF・一般B4は未完成。

## 未完備の実二因子源H0とraw環の代数構造比較計画（2026-10-16）

BS担当でDeltaRootSourceRawH0Algebra.leanを新設する。既存boundedAboveDerivedTensorAlgebraを、元のβ評価とα源写像の
正確な二つのL代数作用で用い、その下層対象が元の実二因子テンソルそのものであることを照合する。
共通derivedH0CommRing・derivedH0AlgebraとderivedTensorH0AlgEquiv、既存の通常テンソル/raw環同型を使用して、
元の実L上のH0とraw環のL代数同型を構成する。元の係数射と標準augmentationによるH0写像を保つ式も証明する。
新たなH0環・実源・一般代数定義を重複せず、既存共通構造を同じ実対象へ適用する。
未完備のH0の比較であり、逐次導来完備化H0との比較・G9による離散性・δ構造の完成とは区別する。ビルド・BS専用監査後に個別コミットする。

## 未完備実源H0の既存raw比較に沿うδ構造接続計画（2026-10-16）

BS担当でDeltaRootSourceRawH0Delta.leanを新設する。前段の同じ実H0の共通環構造と標準raw代数同型を用い、
既存raw δ構造のW2切断を同型の両方向と既存wittTwoMapで共役して、同じ実H0上のδ構造を構成する。
δの具体的座標式、標準H0/raw同型の両方向のδ両立性、元Aの標準係数射との一致とδ両立性を証明する。
新たなH0環・実導来源や一般δ構造移送APIは定義せず、この具体的H0に既存W2構成を適用する。
これは未完備H0のδ構造であり、実導来源全体の離散性や導来δ構造、逐次完備化後H0との比較を結論しない。
任意根族を扱い、G9・G11・正則性・平坦性を仮定しない。ビルド・BS専用監査後に別コミットする。

## 未完備実二因子源H0とraw環の標準代数比較の実装結果（2026-10-16）

DeltaRootSourceRawH0Algebra.leanに4公開宣言を実装した。
元のβ評価・α源写像の正確な二つのL代数作用で、共通の実テンソル代数対象の下層が元の実源そのものであることを照合した。
共通derivedH0CommRing・derivedH0Algebra・derivedTensorH0AlgEquivと既存の通常テンソル/raw環同型から、
同じ実H0とraw環のL代数同型を構成し、積・単位・標準L係数射の両立性を確定した。
その関数が、元の標準augmentationのH0写像と共通の標準single比較の合成そのものである式を証明した。
新たなH0環や実源は定義せず、既存共通構造を同じ実対象へ適用している。
対象3856ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2383宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。未完備H0の環比較であり、逐次完備化H0やG9の離散性の完成とは数えない。
次は同じ標準代数同型と既存W2写像を使う具体的H0のδ構造接続。G9・G11・候補CFF・一般B4は未完成。

## 未完備実源H0のδ構造と標準係数射の実装結果（2026-10-16）

DeltaRootSourceRawH0Delta.leanに5公開宣言を実装した。元の実二因子テンソルのH0にある共通環構造上で、
標準raw代数同型と既存W2写像からδ構造を構成した。δの具体的座標式、同型の両方向のδ両立性、
元Aの標準係数射との一致とそのδ両立性を証明した。任意根族・任意dを扱い、正則性・平坦性・G9・G11を仮定しない。
対象3858ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2388宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。未完備H0上のδ構造であり、実導来源全体の離散性や逐次完備化後H0の比較を結論しない。

G10の到着分も共通正本・NilpotentDerivedReductionとBSの適用先を再確認した。一般APIは完成しており、
DeltaRootFamilySourcePowerInputsで有限根族の実A/(p,dⁿ)還元へ、PrismaticPowerDerivedFlatで一般実prism冪剰余へ、
PerfectPrismDeltaAlgebraPowerInputsで実δ完全化逐次対象の正確な商上G9入力へ既に接続済み。G10本体を重複実装しない。
共通G9は現時点でG9-4までで、最終的な離散性判定は未完成。G11による標準H0比較の完備化後への輸送も別途待つ。
候補CFF・無限根族の全射性への合流・引用なしの一般B4は引き続き未完成。G11のチャット間送信は許可待ちのため実施していない。

## 実源H0から既存prism候補への標準δ射の照合計画（2026-10-16）

BS担当でDeltaRootSourceH0Candidate.leanを新設する。前段の同じ実H0の共通環構造と標準raw代数同型を用い、
既存raw候補射との合成を環射として束ねる。distinguished dの下でこの射のδ両立性を証明し、
標準A係数射を既存候補係数射へ送る式、および元の標準augmentationの実H0写像から得る関数との一致を証明する。
候補の新定義は作らず、既存源・既存候補・元のaugmentationを保持する。完備化後の同型性やCFFを仮定・結論しない。
G9・G11に独立な比較の最後の標準射を確定し、ビルドとpure BS監査後に個別コミットする。

## 実源H0から既存候補への標準δ射の実装結果（2026-10-16）

DeltaRootSourceH0Candidate.leanに4公開宣言を実装した。同じ実H0から既存prism候補への標準raw合成を環射に束ね、
distinguished dの下でそのδ両立性を証明した。元Aの係数射を既存候補の係数射そのものへ送る式と、
元の標準augmentationの実H0写像を使う関数との一致も証明した。任意根族を扱い、G9・G11・平坦性・完備性は仮定しない。
対象4043ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2392宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。候補の新定義を作らず、元の実源・augmentation・既存prism候補を保持した。
未完備H0での標準射の照合であり、完備化後の同型性やCFFを結論しない。
共通G9・G11の状態も再確認し、新たな完成入口はない。両者への具体的入力と適用予定を冒頭の現在の合流点へ整理した。
一般B4は未完成。G11は元のユーザー指定により送信許可待ちで、チャット間送信は実施していない。

## 任意根族の有限座標支持による評価核比較計画（2026-10-16）

BS担当でDeltaDivisionEvaluationFiniteSupport.leanを新設する。任意添字σの既存評価射βと既存座標グラフ関係について、
有限座標集合S⊆σ×ℕの関係イデアルを用い、単調性・有向性・その上限がβの核であることを証明する。
さらにβ(x)=β(y)が一つの有限座標商での標準像の一致で検出できることを証明する。
有限σや可算性を仮定せず、既存一般Ideal/Submodule APIと既存の評価核計算を再利用する。
これは任意根族の有限部分への還元のBS固有入力であり、一般filtered colimitやTor交換を重複実装しない。
実導来還元の離散性・平坦性・候補CFFは別工程。G9・G11と独立にビルド・監査してコミットする。

## 任意根族の有限座標支持による評価核比較の実装結果（2026-10-16）

DeltaDivisionEvaluationFiniteSupport.leanに5公開宣言を実装した。既存β評価と既存座標グラフ関係に対し、
任意σの有限座標集合S⊆σ×ℕから定まる関係イデアル、その単調性と有向性、上限が元の評価核に一致することを証明した。
β(x)=β(y)が、一つの有限座標商における元x,yの標準像の一致と同値であることも証明した。
有限σ・可算性・正則性・完備性・G9・G11を仮定しない。一般の有向上限所属判定はMathlibの既存APIを使用した。
対象3519ジョブ成功、自分のコード警告なし。pure B4監査2397宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次はこの同じ有限商・標準評価射を用い、実評価環を頂点とする標準余極限図式へ接続する。
現状は有限支持での代数的等式検出であり、任意根族の実還元Tor消滅・忠実平坦性や候補CFFを結論しない。
共通CompletionH0Algebra・PrincipalCompletionDerivedComparisonも確認したが、一般G11の代用にはならない。
前者は完備化H0図式、後者は係数環singleの比較を供給し、任意非正対象間のH0同型の完備化後保存は供給しない。
共通G9はG9-4までで最終判定未完成、G11は未送信。一般B4は未完成のまま保持する。

## 任意根族評価の有限座標商の実加群余極限計画（2026-10-16）

BS担当でDeltaDivisionEvaluationFiniteSupportColimit.leanを新設する。既存の有限座標関係イデアルと包含商射から
Finset (σ×ℕ)を添字とする実ModuleCat図式を構成し、元のβで作用する評価環Aへの標準評価余錐を作る。
評価核の上限比較と既存の商核線形同型により、この余錐のIsColimitを証明する。
実圏論的colimitとの標準同型と各段の評価射との可換性も公開する。有限σや可算性、G9・G11は仮定しない。
一般的なfiltered colimit/Tor交換定理は再実装せず、このBS固有図式とその普遍性を確定する。
導来還元のTor消滅・忠実平坦性・候補CFFは未完成として区別し、対象ビルド・BS専用監査後に個別コミットする。

## 共通基盤への要求 G7-Finset：有限部分集合図式での実Tor交換（2026-10-16、送信済み）

対象：可換環R,S:Type u、φ:R→+*S、任意ι:Type u、n:ℕ。要求は
PreservesColimitsOfShape (Finset ι) ((ModuleCat.extendScalars.{u,u,u} φ).leftDerived n)。
遷移射の単射性・全射性、Noether性・有限生成性・可算性は仮定しない。既存の実TorAlg関手と標準余極限比較を使う。
利用工程：B4-6の任意根族。ι=σ×ℕ、R=RelativeFreeDeltaRing σ、
F=deltaDivisionFiniteSupportModuleDiagram D aの各有限座標商から、同じβ作用の評価環へのTor消滅移送。
既存API不足：TorSequentialColimitsのG7入口は添字ℕのPreservesColimitsOfShapeを供給するが、
任意σのFinset (σ×ℕ)には直接適用できない。一般filtered版が既にある場合はその具体的インスタンスの受渡しで足りる。
待つ工程：この具体的図式でのTor/余極限交換。G9・G11の工程とは区別する。
独立作業：有限座標商の余極限のIsColimitはBS側で証明済み。各有限座標集合を有限根部分族・有界δ深さに含める
比較と、その有限根部分族の実残余正則列・Tor消滅の照合を進められる。
一般Tor交換は共通担当の範囲としてBS内で再実装しない。2026-10-16、ユーザーの個別許可を得てCLMSTへ送信済み。

## 任意根族評価の有限座標商の実加群余極限の実装結果（2026-10-16）

DeltaDivisionEvaluationFiniteSupportColimit.leanに9公開宣言を実装した。有限座標集合の包含による標準商線形射と、
Finset (σ×ℕ)を添字とする実ModuleCat図式を構成した。各段から元のβ作用を持つ評価環への標準射と余錐を定義し、
元の評価核の上限計算と既存の商核線形同型を用いてそのIsColimitを証明した。
実圏論的余極限との標準同型と、全有限段の標準評価射を保つ図式も証明した。有限性・可算性・正則性・G9・G11は仮定しない。
対象3522ジョブ成功、自分のコード警告なし。pure B4監査2406宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。既存評価環をそのまま余極限の頂点としており、新しい根添加候補は定義していない。
一般Tor/filtered colimit交換は実装していない。現G7がℕ添字に限定されることを確認し、必要なFinset添字版を
G7-Finsetとして正確に記録したが、送信許可がないため他チャットへは送信していない。
次は各有限座標集合を含む有限根部分族・有界δ深さの比較と、有限部分族での実残余Tor入力を照合する。
任意根族のTor消滅・候補CFF・引用なし一般B4は未完成。共通G9・G11も引き続き別の待合せとして保持する。

## 有限部分根族の係数拡大に向けたδ変数分離計画（2026-10-16）

BS担当でRelativeFreeSubsetSplit.leanを新設する。任意部分集合T⊆σに対し、自由δ座標を
Tの座標と補集合の座標に分離し、後者の自由δ環を係数環とする前者の相対自由δ環への標準代数同型を構成する。
係数・両種類の全δ座標の像を確定し、同型の両方向が既存δ構造と両立することを証明する。
同じ同型が、T内のδ除算反復関係を係数拡大後の同じ反復関係へ送ることも証明する。
新しいδ環・完備化・prismの定義は作らない。この一般δ補助モジュールはBS担当としてBhattScholze内に置く。
有限部分根族の全深さ関係を元の任意σの環で扱うための比較であり、Tor消滅・忠実平坦性をこの同型だけから主張しない。
G9・G11・G7-Finsetから独立に、ビルドとBS専用監査を行って個別コミットする。

部分族分離の同じ実装単位で、有限δ関係イデアルの像、mod(p,d)イデアルの像、
両者の和による実商環同型も照合する。有限根族正則列を元の環へ戻すため、商を具体的に固定する。

## 部分根族と補集合のδ変数分離の実装結果（2026-10-16）

RelativeFreeSubsetSplit.leanに13公開宣言を実装した。任意部分集合T⊆σについて全δ深さを保つ座標分離を構成し、
元の相対自由環を、補集合の相対自由δ環上のTの相対自由δ環へ標準A代数同型で比較した。
係数と両種類の全座標の像、同型の両方向の既存δ構造との両立性、T内の全反復δ除算関係の像を証明した。
有限深さ関係イデアルとmod(p,d)係数イデアルの像、および両者の和による実商環同型も証明した。
有限性・可算性・p正則性・distinguished性・完備性を仮定しない。任意pねじれを許し、空部分族・全体部分族も含む。
対象2061ジョブ成功、自分のコード警告なし。pure B4監査2419宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。反復関係の証明を明示したδ射の等式で行い、高いheartbeat設定なしで検証できた。
次はT有限の場合に既存の有限根族全深さ弱正則列定理を補集合δ環上で適用し、
同じmod(p,d)商比較により元の任意σの環内の有限部分根族へ戻す。初項の弱正則性は元の具体的根関係から供給する。
この分離同型だけからTor消滅・忠実平坦性は推論しない。任意根族のTor消滅、G9・G11の最終適用、候補CFF・一般B4は未完成。

## 任意根族内の有限部分族の全深さ残余正則列計画（2026-10-16）

BS担当でDeltaDivisionFiniteSubfamilyRegular.leanを新設する。部分族Tの補集合の自由δ環を係数に移し、
Tの有限全列挙、元の係数環のp正則性、distinguished単元v、および元の実mod(p,d)商内の有限初項弱正則性から、
同じ元の商内のTの全有限δ深さの連結リストの弱正則性を既存有限根族定理で証明する。
補集合側のp正則性は既存flat移送、ghost単射は既存G4から供給する。外部ghost仮定は追加しない。
具体的根関係の初項正則性を既存deltaRootFirstRelation_mod_pd_fin_isWeaklyRegularで供給し、
任意根族内の有限部分根族の公開弱正則列・Koszul分解を得る。σの有限性・可算性は要求しない。
一般Tor交換・G9・G11は実装せず、この独立なBSの有限段入力をビルド・監査後に個別コミットする。

## 任意根族内の有限部分族の全深さ残余正則列の実装結果（2026-10-16）

DeltaDivisionFiniteSubfamilyRegular.leanに4公開定理を実装した。任意σ、部分集合T、有限全列挙s:Fin m≃Tに対し、
元の実mod(p,d)商内の初項弱正則性・係数環のp正則性・δ(d)を与える単元から、
同じ元の商内のTの全有限δ深さの連結関係列の弱正則性とKoszul分解を証明した。
補集合の自由δ環へ係数を拡大し、既存有限根族定理を適用して元の商へ戻した。
必要なp正則性は既存flat移送、ghost単射は共通G4で供給し、外部ghost仮定は追加していない。
具体的な根関係では既存の任意有限初項正則性定理で初項入力も供給し、元Aのp正則性とδ(d)単元だけで両結論を得た。
σの有限性・可算性・源の離散性・完備性を要求せず、空部分根族も含む。
対象3767ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2423宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次は同じ分離同型で実評価関係を比較し、既存の有限評価関係正則性と
源グラフKoszul/Tor比較へ接続する。現時点は反復δ関係の正則列・Koszul分解であり、
任意根族全源のTor消滅・候補CFF・引用なし一般B4は未完成。G9・G11・G7-Finsetも別の待合せとして保持する。

## 有限部分根族の実評価関係と源グラフTor消滅の接続計画（2026-10-16）

BS担当でDeltaDivisionFiniteSubfamilyTor.leanを新設する。部分族分離同型が実評価関係も保つことを証明し、
既存の有限根族評価関係の弱正則性定理へ、直前の任意σ内の有限部分族の全深さ正則性を供給する。
具体的根関係では初項を既存APIから供給し、実mod(p,d)評価Koszul分解、同じ源グラフ有限商の実Tor比較同型、
その正次数Tor消滅を公開する。σの有限性や可算性を仮定せず、具体的部分族の有限全列挙のみを使う。
一般filtered colimit/Tor交換は実装せず、全源への移送は別工程。ビルドとBS専用監査後に前段と別コミットする。

## 有限部分根族の実評価Koszul分解と源グラフTor消滅の実装結果（2026-10-16）

DeltaDivisionFiniteSubfamilyTor.leanに5公開宣言を実装した。部分族分離同型が全深さの実評価関係も保つことを証明し、
元の実mod(p,d)商内の有限部分族の全深さ弱正則性から、同じ評価関係列の弱正則性を得た。
具体的根関係では、元Aのp正則性とδ(d)を与える単元だけで実残余評価Koszul分解を証明した。
同じ有限部分族・全深さ≤Nの座標列による元の源グラフ商について、実TorAlgと実評価Koszulホモロジーの
比較同型を構成し、正次数Tor消滅を証明した。σの有限性・可算性・d正則性・完備性・外部ghost仮定は要求しない。
対象3770ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2428宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。一般の任意有限座標集合の商のTor消滅を主張しているのではなく、
有限部分根族の全δ深さ≤Nをまとめた具体的な源グラフ商についての結論である。
次は任意有限座標集合がこの形の有限段に含まれることを用いて、先の有限座標商余極限と整合する段を尽くす図式を確定する。
その全源へのTor移送にはG7-Finsetが別途必要。G9・G11も引き続き別工程であり、候補CFF・引用なし一般B4は未完成。

## 全深さ有限部分根族で尽くす評価図式の計画（2026-10-16）

BS担当でDeltaDivisionBoundedSupportColimit.leanを新設する。有限座標集合Sを、その根射影と
δ深さの最大値による有限長方形へ広げる標準操作を構成し、包含・単調性を証明する。
この操作のFinset (σ×ℕ)上の関手が終域余終（Final）であることをMathlibの既存判定で証明し、
先の実有限座標商図式を前合成する。既存評価余錐のwhiskerがIsColimitであること、
同じβ作用を持つ評価環への標準余極限同型と全段の評価射との可換性を公開する。
これにより直前のTor消滅で扱った「有限部分根族・全深さ≤N」の段で、元の評価環を尽くす。
一般Tor交換定理は実装せず、G7-Finsetへの実図式を固定する。ビルド・BS専用監査後に個別コミットする。

## 有界深さ評価図式の各段と全源Tor入力の接続計画（2026-10-16）

BS担当でDeltaDivisionBoundedSupportTor.leanを新設する。標準長方形の有限座標グラフイデアルを、
その根集合の有限全列挙・最大δ深さによる既存源グラフ商と同定する。実加群の同型で直前の有限部分族Tor消滅を移し、
有界深さ評価図式の全段の正次数Tor消滅を追加の仮定なしに証明する。
続いて、この具体的図式に関するPreservesColimitを明示入力として、同じβ作用の全評価環の正次数Tor消滅を証明する。
G7-Finset本体は再実装せず、条件付き全源定理と、無条件の段ごとの定理を区別する。
ビルド・BS専用監査後に余極限図式の区切りと別コミットする。

## 全深さ有限部分根族で尽くす評価図式の実装結果（2026-10-16）

DeltaDivisionBoundedSupportColimit.leanに11公開宣言を実装した。有限座標集合を根射影×有界深さの
全長方形へ広げる操作と、その包含・単調性を証明した。対応するFinset関手のFinal性をMathlibの既存判定で得た。
元の有限座標商図式をこの関手で前合成し、同じβ作用の評価環を頂点とする標準余錐のIsColimitを
既存のFinal関手による余極限保存から証明した。実余極限同型と全段の標準評価射との可換性も証明した。
σの有限性・可算性・正則性・完備性を仮定しない。空座標集合も含む。
対象3550ジョブ成功、自分のコード警告なし。pure B4監査2439宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。次の段ごとのTor接続を別モジュールとして計画・実装中。
任意根族全源のTor移送・G9/G11の最終適用・候補CFF・一般B4は未完成。

## 有界深さ評価図式の全段Tor消滅と全源への接続の実装結果（2026-10-16）

DeltaDivisionBoundedSupportTor.leanに2公開定理を実装した。各標準長方形の根射影を有限全列挙し、
既存の全深さ座標列の範囲がその長方形そのものになることを照合した。源グラフ関係イデアルの一致と
既存の等しい部分加群による商線形同型を使い、実評価図式の各段へ有限部分族の正次数Tor消滅を移した。
公開deltaRootBoundedSupportStage_tor_subsingletonは、元Aのp正則性・δ(d)を与える単元・任意S・正次数i+1から、
元の実mod(p,d)係数射に沿う同じ図式の段のTor消滅を与える。σの有限性・可算性や完備性は要求しない。
公開deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimitは、同じ実図式と実TorAlgの
PreservesColimitを明示入力とし、元のβ作用を持つ全評価環の正次数Tor消滅を証明する。
余極限比較は元の標準評価射から得るものを用い、新しい環や一般Tor交換定理を作っていない。
対象3802ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2441宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。前者の段ごとの消滅はG7-Finset非依存、後者の全源消滅は明示した交換入力に相対的である。
G7-Finsetが渡ればこの入力を直接供給できる。共通G9・G11もなお必要であり、候補CFF・引用なし一般B4は未完成。
G7-Finset・G11は個別の送信許可がなく未送信のまま。計画冒頭の現在の合流点にも待合せを反映した。

## 任意根族の全源Tor入力から元の実係数還元への接続計画（2026-10-16）

BS担当でDeltaRootBoundedSupportResidueDerived.leanを新設する。有界深さ図式での実Tor交換入力を明示し、
既証の任意根族全β評価環のTor消滅を既存Tor対称性でβに沿う実残余終域のTor消滅へ渡す。
元の標準導来augmentationと既存raw残余通常テンソル比較から、同じ実β導来拡大のsingle比較を構成し、順射を明示する。
既存の三因子associator・係数拡大/テンソル比較・実係数制限を再利用して、元の実三因子係数還元のsingle同型、
その標準H0同型と非零次数ホモロジー消滅を証明する。新しい源や導来還元の定義は作らない。
任意根族を扱い、G7-Finset交換入力に相対的な結果として表示する。G9・G11や候補CFFを仮定・結論しない。
対象ビルドとBS専用監査後に個別コミットする。G7-Finsetの送信許可を非同期に確認中であり、まだ送信していない。

## 任意根族の実商環上での純粋性・H0忠実平坦性への接続計画（2026-10-16）

BS担当でDeltaRootBoundedSupportQuotientFlat.leanを新設する。G7-Finset交換入力に相対的に得た元の実三因子係数還元を、
既存の実商環Q=L/(p,d)への底変換と標準係数制限で比較する。Q上の全非零次数消滅、
Q線形H0同型と、元のA/(p,d)上のH0忠実平坦性を証明する。
既存raw残余商の標準A/(p,d)作用と忠実平坦性を再利用し、商代表元の作用を明示する。
既存normalizedPureHomologyIsoにより同じ実Q対象のsingle同型と標準H0の正規化式も公開する。
有限根族の既存APIの置換・弱化はせず、任意σの同じ実対象への条件付き入口を追加する。
導来完備化・G9・G11・候補CFFは結論せず、対象ビルド・BS専用監査後に別コミットする。

## 任意根族の全源Torから元の実係数還元への接続の実装結果（2026-10-16）

DeltaRootBoundedSupportResidueDerived.leanに6公開宣言を実装した。任意根族の有界深さ図式に関する
実Tor/余極限交換入力の下で、既存Tor対称性を使って同じβ拡大のTor消滅を得た。
元の標準導来augmentationと既存raw残余テンソル比較から実β拡大のsingle同型を構成し、順射の標準式も証明した。
元の実三因子係数還元を、既存associator・底変換/テンソル比較・係数制限によって同じraw残余商のsingleへ比較した。
その標準H0同型と全非零次数ホモロジー消滅も証明した。新しい源や導来還元は定義していない。
σの有限性・可算性を仮定せず、交換入力はすべての公開入口で明示した。
対象3830ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2447宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。G7-Finsetに相対的な結果であり、導来完備化後の離散性・候補CFF・一般B4とは区別する。
G7-Finsetのチャット間送信許可を非同期に確認中。元のユーザー指定に従い現時点では未送信。G11も引き続き未送信。
次は同じ元の実商環Q上の純粋性・H0忠実平坦性への接続を検証する。

## 任意根族の実商環上の純粋性・H0忠実平坦性の実装結果（2026-10-16）

DeltaRootBoundedSupportQuotientFlat.leanに8公開宣言を実装した。G7-Finset交換入力を明示し、
元の任意根族の実商環Q=L/(p,d)への底変換対象について、全非零次数ホモロジー消滅、
源作用を保つ係数制限H0同型、実Q線形のH0/raw残余商比較を証明した。
元のA/(p,d)へさらに係数制限した実H0の忠実平坦性を、既存raw残余商の標準係数射と
既存忠実平坦性から移した。商代表元における元の作用を照合し、追加の有限性や外部ghost仮定は入れていない。
同じ実対象のIsGE 0・IsLE 0、既存normalizedPureHomologyIsoによるsingle同型、
その同型のH0が上記の具体的Q線形比較になる正規化式も証明した。
対象3834ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2455宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。任意σを扱うG7-Finset入力に相対的な結果であり、既存の有限根族APIは維持した。
対象は元の未完備実二因子源の商還元であり、完備化後の源の離散性・候補CFF・一般B4を結論していない。
次は同じ任意根族の実A/(p,d)還元・p,d逐次完備化の標準比較への接続を検討する。
G7-Finsetは送信許可を非同期に確認中、G11も未送信であり、両者のチャット間送信は行っていない。共通G9も最終判定待ち。

## 任意根族の元A上の還元と逐次完備化後還元への接続計画（2026-10-16）

BS担当でDeltaRootBoundedSupportPDResidue.leanとDeltaRootBoundedSupportIteratedResidue.leanを新設する。
既存の元Aへの実係数制限/底変換比較を用い、元の実A/(p,d)還元のsingle同型・H0比較・次数零集中・H0忠実平坦性を、
直前の任意根族の実Q還元から導く。既存のp,d逐次主元導来完備化の還元同型を合成し、
同じ逐次完備化対象の実A/(p,d)還元について同じ結論と合成標準単位の可換式を得る。
任意σを扱い、G7-Finset交換入力をすべての入口で明示する。p,d正則性は完備化後の還元比較でのみ要求する。
G9の源の離散性やG11の完備化H0比較は仮定せず、還元比較の完成と区別する。
依存先を含む対象ビルドとBS専用監査を経て、両モジュールをこの接続工程のコミットとして保存する。

## 完全prism上の任意根族についてのG9標準入力の合流計画（2026-10-16）

BS担当でPerfectPrismRootBoundedSupportPowerInputs.leanを新設する。完全prism Pと任意元族b、
有界深さ図式のG7-Finset交換入力から、既証の実逐次源のmod(p,d)次数零集中・H0忠実平坦性を供給する。
既存PrismaticPowerDerivedFlat（共通G10へのBS接続）で同じ実A/(p,dⁿ)還元へ渡し、
標準商比較により同じA/(dⁿ)上の標準mod p実還元の非零次数消滅・H0平坦性を証明する。
共通G8で得た商上p導来完備性と、既存完全prismの係数環pⁿねじれ上界を組み合わせ、
同じ具体的対象についてG9用の4入力を束ね、G9-4の選択モデルの余核消滅も供給する。
σの有限性・可算性や追加単元・ghost仮定は入れず、G7-Finset入力は明示して保持する。
G9本体・G11・候補CFFは未完成として区別し、ビルド・BS専用監査後に個別コミットする。

## 任意根族の元A上の還元と逐次完備化後還元の実装結果（2026-10-16）

DeltaRootBoundedSupportPDResidue.leanとDeltaRootBoundedSupportIteratedResidue.leanに各4、計8公開宣言を実装した。
元の実A/(p,d)還元と標準係数作用付きraw残余商のsingle同型・H0同型・非零次数消滅・H0忠実平坦性を証明した。
同じ元の実源へ既存のp,d逐次主元導来完備化を施し、その実A/(p,d)還元について同じ結論と、
元のp,d合成標準単位の還元とraw比較が可換になる式を証明した。
任意σを扱い、G7-Finset交換入力はすべての入口で明示した。p,d正則性は逐次完備化後の還元比較で要求する。
既存の実底変換・係数制限・逐次完備化比較を再利用し、新しい源や完備化・還元の定義は作っていない。
依存先を含む対象3850ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2463宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。還元での離散性・平坦性であり、逐次完備化源全体の離散性を結論しない。
G7-Finset入力に相対的な成果として保持する。次は共通G10/G8と既存ねじれ評価により、完全prism上の任意根族のG9標準入力へ束ねる。
G9本体・G11・候補CFF・引用なし一般B4は未完成。G7-Finset・G11のチャット間送信は許可がなく未実施。

## 完全prism上の任意根族のG9標準入力の合流結果（2026-10-16）

PerfectPrismRootBoundedSupportPowerInputs.leanに4公開定理を実装した。完全prism P、任意元族b、
有界深さ図式の明示したG7-Finset交換入力から、既存共通G10のprism冪剰余判定を同じ元の実逐次源へ適用し、
実A/(p,dⁿ)還元のIsGE 0・IsLE 0・H0忠実平坦性を証明した。
標準二段商比較から、同じ実A/(dⁿ)対象の標準mod p還元の非零次数消滅とH0平坦性を得た。
既存共通G8の商上p導来完備性と、既存完全prismの係数環pⁿねじれ上界を組み合わせ、
公開perfectPrismRootBoundedSupportPower_G9_inputsに、同じ具体的対象についての4入力を束ねた。
さらにG9-4の選択モデルのp余核複体へ、同じ標準実還元の非零次数消滅を移した。
σの有限性・可算性・追加単元・外部ghost仮定は不要。G7-Finset交換入力は全公開入口で明示した。
対象3912ジョブ成功、自分のコード警告なし（共有既存警告のみ）。pure B4監査2467宣言成功、標準3公理以外なし。
新sorry・公理・外部引用なし。G9の最終離散性判定を供給したのではなく、その正確な対象・商上で必要な入力を供給した。
一般Tor交換は再実装せず、G7-Finsetを待つ。共通G9本体・G11・候補CFF・引用なし一般B4は引き続き未完成。
計画冒頭の現在の合流点も更新し、任意根族について交換入力からG9標準入力までBS側の接続が揃ったことを反映した。
G7-Finset・G11のチャット間送信は許可がなく未実施のまま。

## G7-Finset要求の正式受渡し（2026-10-16）

ユーザーの「G7-Finsetを送ってよい」という個別許可を受け、共通担当の現行「CLMST」チャット
（01a13993-b4ee-7a10-8441-7d21224139d7）へ要求を送信し、送信成功を確認した。
一般APIの正確な型、追加仮定を入れない範囲、現在の逐次G7で不足する点、実際のL・ψ・添字を明示した。
BS側の標準余極限・全段Tor消滅・明示交換入力から実還元とG9標準入力までの接続先、およびpure監査2467宣言も添えた。
受渡し対象はG7-Finsetのみ。G11の送信は今回の許可に含まれず、未送信のまま維持した。
この記録は実装要求の送信完了を意味し、G7-Finsetの実装完了やB4の完成を意味しない。Leanコードは変更していない。

## G11要求の正式受渡し（2026-10-16）

ユーザーの「G11送っても良いです」という個別許可を受け、現行「CLMST」チャット
（01a13993-b4ee-7a10-8441-7d21224139d7）へG11を送信し、送信成功を確認した。
任意の実上有界対象についての同じ上界での非正性保存と、元の射のH0同型を主元導来完備化後へ運ぶ2要求を明示した。
正則性・Noether性・ねじれ有界性・完備性を追加しない範囲と、既存実関手・元の標準射を使うことも伝えた。
BS側の具体的X,Y,fとDeltaRootSourceNonpositiveの証明済み入力、p,dへの逐次適用、
同じ実完備化射・標準単位の既存比較、およびG9の離散性判定とは別工程であることを添えた。
これでG7-Finset・G11の両要求の送信は完了した。両APIの実装完了や一般B4の完成は意味しない。
Leanコードは変更しておらず、今回は送信記録のみ更新した。

## G7-Finset・G9到着後のBS接続計画（2026-10-16）
共通のTorExactColimitsとCompleteFlatReductionBoundedの完成を確認した。
新規BS専用DeltaRootBoundedSupportTorInputs.leanで、任意根族の標準有限部分集合図式のTor交換を供給し、全源Tor消滅の明示交換仮定を外す。
続くPerfectPrismRootPowerDiscrete.leanで、同じ元の実逐次源の生成元冪商へG9を適用し、次数零集中とH0の有界p冪ねじれを証明する。
各段階で対象ビルド・pure BS監査を行い個別コミットする。全源の離散性、G11のH0比較、候補CFF、一般B4とは区別する。

## G7-FinsetのBS適用結果（2026-10-16）
DeltaRootBoundedSupportTorInputs.leanの公開3宣言で、任意根族の標準図式のTor交換と全評価源・実β評価の高次Tor消滅を証明した。
共通torAlg_preservesFinsetColimitsを適用し、従来の明示交換仮定を追加しない入口を供給した。既存条件付きAPIは維持。
対象3873ジョブ成功。pure B4監査2470宣言成功、標準3公理のみ、新sorry・公理・引用なし。
G9の冪商離散性への接続を次段で行う。

## G11のBS実比較射への適用計画（2026-10-16）
共通CompletionUpperBoundがコミット済みとなり、CompletionH0Comparisonにも実H0比較APIが現れた。
BS専用新規DeltaRootSourceCompletionH0.leanで、元の実係数源とraw係数対象のp,d逐次実完備化が非正であること、元のaugmentationを完備化した同じ比較射がH0同型であることを証明する。
共通H0比較APIのビルド・依存監査を確認してから成果を確定する。全源の離散性や候補との環同型はこの結果だけから主張しない。

## G9本体の任意根族の実冪商への適用結果（2026-10-16）
PerfectPrismRootPowerDiscrete.leanの公開2定理で、任意根族の元の実逐次源をA/(d^n)へ実還元した対象の次数零集中、H0の有界p冪ねじれ、非零次数ホモロジー消滅を証明した（n>0）。
完成した共通G9本体に、既存G10/G8・完全prismの係数ねじれ評価・新G7無条件交換を同じ対象で適用した。
σの有限性・可算性や明示Tor交換仮定は不要。対象3963ジョブ成功、pure B4監査2472宣言成功、標準3公理のみ。
これは全生成元冪商の離散性であり、全源自体の離散性・候補CFF・一般B4はなお別工程である。

## G11の元の標準比較射への適用結果（2026-10-16）
共通CompletionH0Comparisonは556c76beで完成。DeltaRootSourceCompletionH0.leanの公開5宣言で元の実源とraw係数対象の逐次完備化の非正性、同じaugmentationのp完備化・p,d逐次完備化後のH0同型、およびその標準射が誘導する具体的H0同型を証明した。
σ,dの追加仮定は不要。対象3868ジョブ成功、pure B4監査2477宣言成功、標準3公理のみ。
これは同じ係数A上の実逐次完備化どうしのH0同型であり、raw環自身のPD完備化H0との環・δ構造比較は次段である。

## 実逐次源全体の離散性への接続計画（2026-10-16）
全生成元冪商の離散性とG11による源の非正性が揃ったので、BS専用新規PerfectPrismRootSourceDiscrete.leanで元の実逐次源自体の離散性を証明する。
生成元正則性による既存powerCokernelReconstructionと既存Milnor射の単射性を適用し、負次数は各冪商の消滅から、正次数はG11から消す。
一般の完備性・Tor補題は新設せず、任意根族のこの具体的対象に限って接続する。環・δ構造比較と候補CFFは別工程である。

## 元の実逐次源全体の離散性の接続結果（2026-10-16）
PerfectPrismRootSourceDiscrete.leanの公開5宣言で、完全prism上の任意根族の元の実逐次完備化源そのものの離散性を証明した。
各生成元冪余核の負次数消滅（零冪を含む）を、生成元正則性による既存再構成と既存Milnor射の単射性で源へ戻し、正次数はG11で消した。
同じ実H0のsingle対象への同型を恒等H0で正規化した。σの有限性・可算性、追加Tor交換仮定は不要。
対象4013ジョブ成功、pure B4監査2482宣言成功、標準3公理のみ。新sorry・公理・外部引用なし。
G7-Finset・G9本体・G11の待合せは解消し、BS側の任意根族への適用を完了した。
次はrawのA上の実逐次完備化H0とraw環上のPD完備化H0の標準比較、環・δ構造との照合、候補CFF・根付き拡大の存在である。
一般B4の引用なし全射性はまだ未完成。André引用に相対的な成果は従来どおり区別し、B-I/B6引用も維持する。

## raw環上の実完備化への係数比較計画（2026-10-16）
新規BS専用DeltaRootRawCompletionRestriction.leanで、raw係数対象を実際の係数射A→Rawによるsingle Rawの係数制限と照合する。
共通G8をp,dの順で適用し、既存A上のraw逐次完備化とraw環上の逐次実完備化を同型にする。標準単位とH0比較を公開し、続くPD完備化との照合の入力にする。
一般の係数制限・完備化補題は重複実装しない。各検証済み工程だけ個別コミットする。

## raw環上の実逐次完備化への係数比較結果（2026-10-16）
DeltaRootRawCompletionRestriction.leanの公開6宣言で、標準係数射A→Rawに沿う元のraw singleの比較、G8を二度適用した実逐次対象の同型、元の二つの標準単位の図式、H0比較を証明した。
元の実根添加源H0からraw環上の実逐次完備化H0への具体的A線形同型を供給した。任意σ・dで追加仮定なし。
対象4055ジョブ成功、pure B4監査2488宣言成功、標準3公理のみ。PD環とのH0・環構造比較は続く工程。

## raw実H0とPD完備化H0の反射比較計画（2026-10-16）
新規BS専用DeltaRootRawCompletionReflection.leanでraw環上の実逐次完備化H0の二座標完備性と、同じ標準単位での完備加群への反射性を証明する。
共通G11のH0反射と既存の二座標Koszul H0反射を用い、元の単位を保つRaw線形同型をPDCompletionH0へ構成する。
一般の完備性や反射の定義は既存APIを使い、原典の導来完備化を古典的完備化へ置き換えない。

## raw実H0とPD完備化H0の反射比較結果（2026-10-16）
DeltaRootRawCompletionReflection.leanの公開8宣言で、raw環上の実逐次対象の二座標完備性、実H0の同じ線形単位による完備加群への反射性を証明した。
二つの実H0反射の普遍性からRaw線形同型を構成し、全raw係数の標準像を保つことを証明した。
元の実根添加源H0からrawのPDCompletionH0への具体的A線形同型deltaRootSourcePDH0Isoを公開した。
追加正則性・有限性・古典的完備性仮定なし。対象4056ジョブ成功、pure B4監査2496宣言成功、標準3公理のみ。
環・δ構造との照合、候補CFF・根付き拡大の存在、一般B4は引き続く工程。

## raw実逐次H0の環構造との照合計画（2026-10-16）
新規BS専用DeltaRootRawCompletedH0Ring.leanで、同じ実H0の元の加法・Raw作用を保つ既存反射環構造を使い、上の正規化線形同型をRaw代数同型へ上げる。
標準単位を保つことと既存reflection.linearMap_map_mulによる積の一致を証明し、実PD完備化環との同定を公開する。
共通の環・反射定義は再実装しない。δ構造との照合と候補CFFは後続工程。

## raw実逐次H0の環構造との照合結果（2026-10-16）
DeltaRootRawCompletedH0Ring.leanの公開5宣言で、元の実H0の加法・Raw作用を保つ既存反射環・代数構造を設定し、同じ線形比較がRaw代数同型になることを証明した。
その関数は既存の正規化線形比較そのものであり、全raw係数を元のpdCompletionUnitの像へ送る。
対象4057ジョブ成功、pure B4監査2501宣言成功、標準3公理のみ。新sorry・公理・外部引用なし。
次は源の離散性とA線形PD比較から実PD環の(p,d)完全忠実平坦性へ移し、δ完全化後の候補CFFへ進む。

## 実PD環の完全忠実平坦性への接続計画（2026-10-16）
新規BS専用PerfectPrismRootPDCompletelyFlat.leanで、元の実逐次源の離散性と実PD H0比較からsingle PD対象への同型を構成する。
既証の同じ実(p,d)還元の次数零集中・H0忠実平坦性をPD係数加群へ移し、共通isCompletelyFlat_of_acyclic_flat_reductionを適用する。
任意根族の実PD環について(p,d)完全忠実平坦性を公開し、δ完全化後の既存候補の平坦性とは区別する。

## 任意根族の実PD環の完全忠実平坦性の接続結果（2026-10-16）
PerfectPrismRootPDCompletelyFlat.leanの公開6宣言で、完全prism上の任意根族の実PD完備化環が元の(p,d)に関して完全忠実平坦であることを証明した。
元の実逐次源の離散性・実PD H0比較から同じ標準A作用付きPD係数加群のsingle対象への同型を構成し、既証の実還元の非零次数消滅・H0忠実平坦性を移した。
共通の実係数拡大/Tor・通常係数拡大の比較とisCompletelyFlat_of_acyclic_flat_reductionを使用。具体的な制限係数加群を公開型に保ち、追加Tor交換・有限性・古典的完備性仮定なし。
対象4187ジョブ成功、自分のコード警告なし。pure B4監査2507宣言成功、標準3公理のみ、新sorry・公理・引用なし。
δ完全化後の既存prism候補のCFF、任意根族の根付き拡大の存在、引用なしの一般B4は未完成であり、André条件付き成果とは引き続き区別する。
計画冒頭の現在の合流点も実PD環の完全忠実平坦性まで更新した。

## 実δ完全化逐次対象の離散性の合流計画（2026-10-16）
新規BS専用PerfectPrismDeltaAlgebraDiscrete.leanで、既存の具体的δ完全化逐次対象に共通G9本体とG11を適用する。
元のδ代数の(p,d)実還元の次数零集中・H0忠実平坦性を明示入力とし、生成元冪商の離散性・H0有界p冪ねじれ、全実逐次対象の離散性を証明する。
既存G8/G10標準入力、冪余核再構成・Milnor射を使う。続いて実根PD環の既証入力を供給し、δ完全化後の候補へ接続する。

## 実根PD環からδ完全化離散性への具体的合流計画（2026-10-16）
新規BS専用PerfectPrismRootPDPerfectionInputs.leanで、既証の実PD係数加群と標準係数射A→PDCompletionH0の制限加群を同定する。
標準係数射のδ射性と、同じ(p,d)実還元の非零次数消滅・H0忠実平坦性を供給し、PerfectPrismDeltaAlgebraDiscreteの実逐次δ完全化対象の離散性を具体的な根PD環へ適用する。
δ完全化後の実PD環自身とのH0同定と候補CFFは後続工程であり、入力への追加仮定として隠さない。

## 実δ完全化逐次対象の離散性の合流結果（2026-10-16）
PerfectPrismDeltaAlgebraDiscrete.leanの公開5宣言で、元のδ代数の実還元入力から、同じ実δ完全化逐次対象の全生成元冪商の離散性・H0有界p冪ねじれと、全対象の離散性・実H0のsingle比較を証明した。
既存G8/G10/G9/G11と再構成・Milnor射を使用。対象3965ジョブ成功、pure B4監査2512宣言成功、標準3公理のみ。根PD環からの具体的入力供給を次段で行う。

## 逐次PD実H0反射の証明共有計画（2026-10-16）
raw環に実装済みの二座標実H0反射・PD線形比較を、δ完全化環でも同じ証明を複製せず使うため、新規BS専用IteratedPDH0Reflection.leanへ一般の環R・自然数p・元dの形で抽出する（担当BS、配置BhattScholze内）。
DeltaRootRawCompletionReflection.leanの既存公開型・単位規約を維持し、抽出した同じ証明の特殊化へ置き換える。
共通層は編集しない。共通G11の一座標反射・F3の二座標反射を再利用し、同等の基礎定義は新設しない。
抽出のビルド・全BS依存監査後、δ完全化後の実PD H0比較へ利用する。

## 実根PD環からδ完全化離散性への具体的合流結果（2026-10-16）
PerfectPrismRootPDPerfectionInputs.leanの公開6宣言で、実PD係数加群と同じ標準環射に沿う加群の同型、標準係数射のδ射性、実還元の次数零集中・H0忠実平坦性を証明した。
それらを一般δ完全化のG9/G11離散性判定へ供給し、任意根族のPD環をδ完全化した同じ実逐次対象の離散性と、全生成元冪商の離散性・H0有界p冪ねじれを証明した。
追加有限性・Tor交換・古典的完備性仮定なし。対象4214ジョブ成功、pure B4監査2518宣言成功、標準3公理のみ。
δ完全化後の実PD H0・既存候補への比較と候補CFFは引き続く工程。

## 実δ完全化H0から直接PD H0への比較計画（2026-10-16）
新規BS専用DeltaAlgebraPerfectionPDH0Comparison.leanで、既存G8のδ完全化逐次H0比較と抽出した同じ二座標反射を合成する。
δ完全化環Cの実PD H0の元のC加群作用と、標準係数射A→C→PDによるA作用を同定し、元の実δ完全化逐次対象H0からその正確なPD係数加群へのA線形同型を公開する。
抽象的な存在だけを仮定せず、具体的なC・係数射・標準単位に基づく構成を使用する。次に既証離散性と組み合わせて実還元・CFFを移送する。

## 逐次PD実H0反射の証明共有結果（2026-10-16）
IteratedPDH0Reflection.leanの公開8宣言へ、二座標実H0反射・PD線形比較の既存証明を抽出した。
元の第一座標fと標準単位を保持し、f=pという明示等式から実PD H0との同型を得るため、係数射の像を無断で置換する問題を避けた。
DeltaRootRawCompletionReflection.leanの既存公開型・単位を保ち、その4証明を特殊化へ置き換えた。重複していた本体73行を除去した。
既存の実根PD環の環比較・CFF・δ完全化入力まで再ビルド4215ジョブ成功。pure B4監査2526宣言成功、標準3公理のみ。
共有ファイルは編集していない。次は抽出した同じ証明をδ完全化環Cへ適用する。

## δ完全化後の実PD環の完全忠実平坦性への接続計画（2026-10-16）
新規BS専用PerfectPrismDeltaAlgebraPDCompletelyFlat.leanで、元δ代数の明示実還元入力から、実δ完全化逐次対象の離散性と新H0比較により、標準係数射A→C→PDのsingle対象との同型を構成する。
同じ実(p,d)還元の消滅・H0忠実平坦性を移し、共通の実Tor・通常係数拡大比較と完全平坦性判定により、その正確な標準係数作用で実PD環の完全忠実平坦性を証明する。
根PD環から供給済みの具体的入力へ続いて適用し、既存候補との標準同型で移送する。

## 実δ完全化H0から直接PD H0への比較結果（2026-10-16）
DeltaAlgebraPerfectionPDH0Comparison.leanの公開3宣言で、既存G8と同じ二座標実反射を合成し、実δ完全化逐次H0をC上の実PD H0の係数制限および標準合成射A→C→PDの加群と同定した。
Cの元の加群作用と合成環準同型の作用は具体的な恒等線形同型で照合した。追加正則性・有限性・完備性仮定なし。
対象3981ジョブ成功、pure B4監査2529宣言成功、標準3公理のみ。次は離散性と合成しPD環の実還元とCFFを移送する。

## 既存根prism候補のCFFへの移送計画（2026-10-16）
新規BS専用PerfectPrismRootPrismCompletelyFlat.leanで、具体的根PD環の既証入力を実δ完全化後のPD環の完全忠実平坦性へ供給する。
既存deltaRootPDCompletedPerfectionEquivの標準係数射の可換性から、同じA作用を持つ係数加群の線形同型を構成する。
同じ(p,d)残余Tor消滅・通常係数拡大の忠実平坦性を移送し、既存prism台環候補の標準係数射について完全忠実平坦性を公開する。
その生成元商のp完全忠実平坦性と任意根族の根付きperfectoid拡大は次段と区別する。

## δ完全化後の実PD環の完全忠実平坦性の結果（2026-10-16）
PerfectPrismDeltaAlgebraPDCompletelyFlat.leanの公開6宣言で、元δ代数の実還元入力から、標準係数射A→δ完全化→PDを持つ実PD環の(p,d)完全忠実平坦性を証明した。
同じ実逐次対象の離散性とH0比較をsingle同型に合成し、元の実還元の消滅・H0忠実平坦性を移した。Tor・通常係数拡大・完全平坦性の共通APIを使用。
対象4007ジョブ成功、pure B4監査2535宣言成功、標準3公理のみ。根PD環への具体的適用と既存候補への移送を次段で行う。

## 既存根prism台環候補のCFFへの移送結果（2026-10-16）
PerfectPrismRootPrismCompletelyFlat.leanの公開5宣言で、任意根族の実根PD環のδ完全化・実PD完備化の標準A作用が(p,d)完全忠実平坦であることを証明した。
既存deltaRootPDCompletedPerfectionEquivとその標準係数射の図式から、既存候補との同じA作用付き線形同型を構成し、残余Tor消滅・通常係数拡大の忠実平坦性を移した。
既存根prism台環候補の標準係数射の(p,d)完全忠実平坦性perfectPrismRootPrism_isCompletelyFaithfullyFlatを公開した。
対象4226ジョブ成功、自分のコード警告なし。pure B4監査2540宣言成功、標準3公理のみ。新sorry・公理・外部引用なし。
次は生成元商のp完全忠実平坦性へ降ろし、既存の互換根族・perfectoid性と束ねて任意根族の根付き拡大の具体的存在へ進む。
一般B4の全射性は未完成。André引用に相対的な結果とは引き続き区別し、B-I/B6引用も変更していない。
計画冒頭の現在の合流点を既存prism台環候補のCFFまで更新した。

## 生成元商の実mod p還元への移送計画（2026-10-16）
新規BS専用PrismaticGeneratorPowerModPFaithful.leanで既存の二段階実還元同型に沿ってH0忠実平坦性を移す。平坦性のみの既存入口を維持する。
続く新規PerfectPrismRootQuotientReduction.leanで、候補prismの生成元正則性と元の生成元正則性から実生成元商を通常商singleへ同定する。
商のA/(d)作用は既存deltaRootPerfectoidCandidateBaseMapを使い、通常係数拡大との同型を標準代表上で照合する。
これらから候補perfectoid商のp完全忠実平坦性を実Tor判定で証明する。共有基盤は編集しない。

## perfectoid候補商のp完全忠実平坦性の実装計画（2026-10-16）
新規BS専用PerfectPrismRootPerfectoidCompletelyFlat.leanで、既存根prismの(p,d)実還元の次数消滅・H0忠実平坦性を、二段階商比較と生成元商single同型でperfectoid候補のmod p実還元へ移す。
その同じA/(d)基底射の高次Tor消滅・通常剰余係数拡大の忠実平坦性を供給し、共通完全平坦性判定でp完全忠実平坦性を証明する。
生成元商にp正則性を追加せず、元のperfectoid候補のpねじれと零環を許す。

## 生成元商の実mod p還元への移送の入力結果（2026-10-16）
PrismaticGeneratorPowerModPFaithful.leanの公開1定理で、既存の標準商同型に沿い実mod p還元H0の忠実平坦性を移した。
PerfectPrismRootQuotientReduction.leanの公開4宣言で、既存prism候補の元Aのd作用の正則性、実生成元商のTor消滅、通常係数拡大と既存perfectoid商の基底射の同型、同じ実生成元還元と通常商singleの同型を証明した。
両対象ビルド成功（根商4227ジョブ）。pure B4監査2545宣言成功、標準3公理のみ。新sorry・公理・外部引用なし。
次はこれらを同じ実mod p還元へ適用し、perfectoid候補の標準基底射のp完全忠実平坦性を証明する。

## 根付きperfectoid拡大と一般B4の最終合流計画（2026-10-16）
新規BS専用PerfectPrismRootedPerfectoidExtension.leanで、候補商の同じ基底射のp完全忠実平坦性を通常のAlgebra作用でも公開し、任意のA/(d)内の族の代表を選んで、具体的perfectoid拡大・係数射・互換根族を束ねた存在定理を証明する。
同じモジュールで既証の根付き核降下を適用し、完全prism商からの導来p完備全射商の任意perfectoid化の全射性を証明する。
続く新規SemiperfectoidSurjectivity.leanで既存perfectoidTrialPrismの商表示を用い、任意perfectoid源へ移す。源の環同型は全射qとの合成に吸収し、CFFの新しい基底変更定義を追加しない。零環枝も処理する。
B3の存在・普遍性と合成して全射perfectoid化の存在も供給する。André引用・B-I/B6引用に戻らず、公開定理の全依存をpure監査する。

## perfectoid候補商のp完全忠実平坦性の結果（2026-10-16）
PerfectPrismRootPerfectoidCompletelyFlat.leanの公開7宣言で、任意根族の既存perfectoid候補商の標準基底射A/(d)→候補についてp完全忠実平坦性を証明した。
元のprismの(p,d)還元から、既存の二段階商比較と生成元商single同型を経て、同じ商のmod p実還元の消滅・H0忠実平坦性、Tor消滅、通常係数拡大の忠実平坦性を供給した。
生成元商のp正則性や有限性は仮定していない。対象4229ジョブ成功、pure B4監査2552宣言成功、標準3公理のみ。
先の忠実平坦性補題の長行警告も解消した。新sorry・公理・引用なし。次は任意根族の拡大存在と既証降下への最終合流。

## 根付きperfectoid拡大と完全prism商での全射性の結果（2026-10-16）
PerfectPrismRootedPerfectoidExtension.leanの公開3宣言で、同じ標準基底代数作用のp完全忠実平坦性と、完全prism商内の任意元族の互換根を備える具体的perfectoid拡大の存在を証明した。
元の核の全元を添字族として、既存の根付き核降下を適用し、完全prism商からの導来p完備全射商の任意IsPerfectoidizationの全射性を証明した。
対象4283ジョブ成功、pure B4監査2555宣言成功、標準3公理のみ。André・B-I/B6・全射性引用への依存なし。
一般perfectoid源への商表示を通じた移送と旧B-S入口の解消を残す。

## B4-7の既存B-S入口の最終接続計画（2026-10-16）
任意perfectoid源・導来p完備全射商・任意IsPerfectoidizationの一般全射性と、B3と合成した全射perfectoid化の存在がビルド済みとなった。
pねじれのない古典的完備商の既存Inputs/SemiperfectoidSurjectivity.leanの同じ署名を維持し、一般存在定理と既存の正則な場合の古典的/導来完備性比較により既存sorryを証明へ置き換える。
既存PerfectoidizationSurjectivity.leanの公開APIは維持し、文献引用とする説明のみ証明済みの入口へ更新する。これらはいずれもBS専用ファイル。
新一般定理の842到達モジュールに旧B-S入力のimportがなく循環しないことを確認済み。一般定理・旧B-S存在API・任意普遍対象への旧移送APIをpure監査し、CLMST/CyclicPerfectoidizationのビルドで利用先との互換性を確認する（利用先は編集しない）。
B-I/B6とAndréの既存引用は変更しない。

## 一般B4の公開定理の証明結果（2026-10-16）
SemiperfectoidSurjectivity.leanの公開3定理で、任意perfectoid源・導来p完備全射商の任意IsPerfectoidizationの全射性を証明した。
非零源は既存のFontaine/完全prism商表示を用い全射qと商表示を合成して完全prism商での既証全射性へ移し、零環枝も処理した。
B3と合成して一般の全射perfectoid化の存在も証明し、古典的p進完備商の互換入口も共通の完備性比較から証明した。p正則性・有限性・古典的完備性を一般入口へ追加していない。
対象4284ジョブ成功、pure B4監査2558宣言成功、標準3公理のみ。André・B-I/B6・旧B-S引用への依存なし。
B4-7の残作業は既存B-S引用入口の同じ署名での証明置換・旧利用入口のビルドと監査・最終完了記録である。

## B4-7最終完了監査（2026-10-16）
B4は引用なしで完成。SemiperfectoidSurjectivity.leanの一般定理の型は、任意R,S,C、素数p、hR:IsIntegralPerfectoid R p、全射q:R→S、hS:IsModuleComplete S p (ModuleCat.of S S)、任意f:S→Cとhf:IsPerfectoidization p fからFunction.Surjective f。
零環枝と一般pねじれ商を含み、p正則性・有限生成性・古典的完備性を一般定理の仮定に追加していない。
B3の存在・普遍性から同じ一般性で全射perfectoid化の存在も供給した。完全prism商の任意元族について具体的p CFF perfectoid拡大・標準係数射・互換根を構成し、元の核全体への適用と既証降下で証明した。
旧Inputs/SemiperfectoidSurjectivity.leanのB-S sorryは同じ公開署名の証明へ置換済み。正則な場合の古典的/導来完備性比較も既存共通APIで証明済みのものを使用した。
旧任意普遍対象への移送APIとCLMST/CyclicPerfectoidizationを含む対象ビルド4363ジョブ成功。pure B4監査2560宣言成功、標準3公理propext・Classical.choice・Quot.soundのみ、新sorry・公理・外部引用なし。
旧B-S入力に戻るimport経路がなく循環依存なし。CLMST・共有基盤・RootTower・Serre利用先・ルートimport・共有監査は編集せず、BS専用コード・計画・監査のみ更新した。
André条件付き定理は条件付きのまま保持するが一般B4には依存しない。B-I/B6引用も維持。B5はこの完了範囲に含めない。
