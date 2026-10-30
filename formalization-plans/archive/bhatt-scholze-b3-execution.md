# B3一般存在・普遍性の実行計画

> **アーカイブ（2026-10-17）**：この計画は完了した。内容の要約先：解説の付録 A（`par:bs-thm74`）と `BhattScholze/` の各モジュールの docstring。原典の証明経路は[BS 主計画](../bhatt-scholze/bhatt-scholze.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


2026-10-14。BS主計画のB3に関する実行記録。
状態：一般B3の存在・IsPerfectoidization普遍性は証明・監査済み。
原典Prop 7.2の全prism始対象、B4の全射性、B5の冪等性は別の未完了工程。
目標は任意のperfectoid環Rの導来p完備な商Sに対する、具体的な写像S→Cの
IsPerfectoidization。全射性はB4に分ける。標数p特殊場合だけで一般B3を完了とはしない。

## 最終受渡しと受入条件

p:ℕは素数、R,S:Type uは可換環、hR:IsIntegralPerfectoid R p、
q:R→Sは全射、Sは既存IsModuleComplete S (p:S) (ModuleCat.of S S)を満たす。
結論は∃C:Type u, ∃CommRing C, ∃f:S→C, IsPerfectoidization p f。
Sのp正則性・有界ねじれ・古典的完備性・Noether性・有限表示性を追加しない。
別の系でp正則な古典的完備商を扱う場合は既存比較を明示して導来条件を供給する。

存在、Cのperfectoid性、試験perfectoid環Tへの一意延長を証明する。
既存IsIntegralPerfectoid/IsPerfectoidizationと一意性・核一致APIを再利用する。
B-I/B-S/B-R/André引用はこの存在証明の依存へ持ち込まない。
各段階を対象ビルド・BS監査・依存監査で検証し、検証済みの自分の変更だけをコミットする。

## 受領状況

- F3：受領済み。実際のKoszul H⁰へのδ延長P1〜P3もBS側で証明済み。
- F4：共通計画§9.4で完了。Witt復元・零環の枝・標準商図式・一意持上げを再監査して利用する。
- F5：共通計画§9.3で完了。有界ねじれ商のp完備性を再監査し、既存BSのN=1/N=nを供給する。
- F6：受領済み。一般の主イデアル商のperfection核をBSの標準tilt射へ接続した。
- F7：共通側でp正則perfectoid環の核進分離性まで完了。今回のB3の一般pねじれ入力には利用せず、F6からの比較同型で進めた。
- ω₁に関する導来完備性保存：F3本体とは別の接続条件。一般比較は共通要求に記録する。

共有ファイル・CLMST・RootTower・利用先・ルートimport・共有監査は編集しない。
他チャットへのメッセージは送らない。新しいsorry・公理・引用は追加しない。

## ステップと終了条件

| 順 | 工程 | 具体的終了条件 |
| --- | --- | --- |
| B3-1 | P4：原典の一段操作 | δ除算・旧ねじれ商・実H⁰の具体的環と射、一意δ延長 |
| B3-2 | F4/F5のBS接続 | 完全δ環のWitt表示とdistinguished商・冪商のp完備性 |
| B3-3 | Lemma 3.9の完全化 | 生成元・正則性・実完備性・完全δ構造・完全prismへの普遍性 |
| B3-4 | Theorem 3.10の一般対応 | 一般完全prism商のperfectoid性、任意perfectoid環の対応と射 |
| B3-5 | Prop 7.2のsuccessor・極限 | 具体的δ図式、旧ねじれの消滅、余極限の等式検出、宇宙管理 |
| B3-6 | 安定化と始対象 | 最終d正則性・実完備性・prism性、Lemma 3.5/4.8の試験対象への接続 |
| B3-7 | Cor 7.3と公開存在 | 任意S・任意試験perfectoid TのIsPerfectoidization、存在の公開定理 |

B3-2〜4とB3-5〜6には独立に進められる部分があり、一方の不足で他方を停止しない。
実際の反復構成の不足はbhatt-scholze-prop72-construction.mdに記載した型で解消する。
一段の完備化後のd正則性、全遷移射の単射性、全極限段の完備性を暗黙に仮定しない。

## B3-1の型

予定：`BhattScholze/DeltaDivisionPDCompletion.lean`。
D:DeltaStructure p R、d:R、a:σ→R、σ:Type u（Jの全元を含む）とする。
U=DeltaDivisionTorsionQuotient D d a、d_Uは既存基底射のdの像。
C=PDCompletionH0 U p d_U。F3の環構造とP3のδ構造をそのまま使う。

試験δ環(E,T)、基底δ射f:R→T、f(d)倍が単射、全sでf(d)∣f(a_s)、
T自身がp,f(d)実導来完備なら、C→Tの一意δ延長を得る。
Cの実p,d完備性と基底射のδ性を公開する。
dがdistinguishedならその像もdistinguishedだが、C内のd正則性はまだ結論しない。

## 証明経路の管理

正本の原典経路はProp 7.2→Lemma 3.9→Theorem 3.10→Cor 7.3。
完備化と完全化の順序を変える候補は、完全試験prismへの一意普遍性・
生成元正則性・実完備性・既存公開型への接続をすべて証明するまで採用しない。
候補の同型や標数pの存在を、一般B3の代替完成として扱わない。

B3完了の監査では、一般のpねじれ商を含む上記最終入力をそのまま確認する。
有限生成イデアル、pねじれのない商、選んだ特殊prismだけへの制限は完成条件を満たさない。
新しい存在定理の依存に既存B-I/B-Sがないことを推移的に確認する。

## B3-1/P4実装完了（2026-10-14）

`DeltaDivisionPDCompletion.lean`で、任意の元族（Jの全元を含む）の除算添加、
旧ねじれのδ閉包商、実PDCompletionH0の一段を構成した。
具体的環構造・δ構造・標準射、実p/d完備性、distinguished像、
添加元の可除性・生成イデアルの包含、一意δ延長を公開した。
一段候補のd正則性は未結論であり、Prop 7.2全体とは区別する。
対象ビルド・BS監査・全体ビルド（4329ジョブ）成功。
import閉包99モジュール、Inputs・CLMST・Paper・RootTower依存なし。
新規sorry・公理・引用なし。

## B3-2：F4/F5接続（2026-10-14）

`PerfectDeltaWittRecovery.lean`：完全δ構造からp正則性・mod p完全性を供給し、
F4のWitt復元同型と標準商図式を公開した。同型そのものは零環を含む。
標準Witt δ構造との順逆比較ではModPのCharPを明示する。
任意の標準Witt環からp正則p進完備δ環への環射がδ射となることも、
共通Witt持上げの一意性で証明した。連続性は追加仮定にしない。

`DistinguishedQuotientComplete.lean`：既存のN=1/N=kねじれ評価をF5へ渡し、
distinguished商と全冪商の古典的p完備性を公開した。
商のp正則性・Noether性・有限表示性は不要。冪指数0も含む。

対象ビルド・BS監査・全体ビルド（4330ジョブ）成功。
新規7公開宣言の公理依存はpropext・Classical.choice・Quot.soundのみ。
import閉包は16/60モジュール、Inputs・CLMST・Paper・RootTower依存なし。
新規sorry・公理・引用なし。
次はLemma 3.9の完備化後の完全δ性・正則性・完全prism普遍性。

## B3-3：完全δ基底の実完備化の核心（2026-10-14）

`DeltaFrobeniusComplete`に逆向きの完備性接続を追加した。
p,f(φ(d))実導来完備からf(d)実導来完備を導き、正冪と元の局所化の同型を使う。
一般の古典的完備化へ置き換えず、既存の実導来対象を比較する。

`PerfectDeltaPDCompletion.lean`で、完全δ基底の実PDCompletionH0の完全δ性を証明。
逆Frobeniusをδ普遍性で延長し、両合成を環普遍性で恒等射と判定する。
源の古典的完備性を要求しない。

`PerfectDeltaPDPrism.lean`で、distinguished dの実H⁰上の具体的完全prismを構成。
完全δ性からp正則性、F2からp古典的完備性、Lemma 2.34からd像の正則性を供給。
実p,d完備性を記録し、F5で標準商のp完備性も証明する。
`PerfectDeltaPDPrismUniversal.lean`で、dをイデアルへ送る基底δ射について
完全試験prismへの唯一のprism射を証明した。orientationの厳密な保存は要求しない。

追加8公開宣言のBS監査、個別ビルド、全体ビルド（4335ジョブ）が成功。
import閉包104モジュールにInputs・CLMST・Paper・RootTower依存なし。
新規sorry・公理・引用なし。
一般prismからの前処理・完全化全体、一般perfectoid対応、原典Prop 7.2の
一般始対象と最終B3の受渡しはまだ未完了。完全δ基底の場合の核心と区別する。

## B3-3追加：完全試験prismへの除算候補（2026-10-14）

`PerfectDeltaDivisionPrism`と`PerfectDeltaDivisionQuotient`で、任意のイデアルJの全元を
除算添加し、p進完備δ完全化と実PD完備化を合成した具体的な完全prismを構成した。
生成元は元のdの標準像で、完全試験prismへの一意延長、Jの像の包含、
元の商からprism商への標準射、prism商のp完備性を証明した。
一般prismの始対象やIsPerfectoidizationはまだ結論しない。

12公開宣言のBS専用監査と全体ビルド（4341ジョブ）成功。
新しいsorry・公理・引用なし。一般B3の完成ではなく、次の対応証明へ渡す候補である。

## B3-4/F6：一般の完備Witt商（2026-10-14）

`WittQuotientTiltKernel`でF6の一般核計算を標準tilt射へ移した。
`WittQuotientTiltSurjective`で、像元によるtiltの分離性と係数環の完備性から全射性を証明。
`WittQuotientTiltEquiv`で、Witt環のd完備性からmod pの被約性とF5を介して
係数環のd₀完備性を供給し、既存の単射性と全射性を合成した。
`WittCompleteQuotientPerfectoid`で、標準Fontaine比較射の同型から核を移し、
一般のdistinguished商のIsIntegralPerfectoidを証明した。零環とpねじれ商を含む。
商のp正則性・d₀の正則性・F7・既存B-I/B-S引用を使わない。

新規9公開宣言の個別ビルドとBS専用監査が成功。
公理依存はpropext・Classical.choice・Quot.soundのみ。
これから一般完全prismへ移送し、任意試験perfectoid環の対応と射へ進む。

## B3-4追加：一般の完全prism商（2026-10-14）

`FontaineNaturality`で共通Witt持上げ一意性からFontaine射の自然性を証明。
`PerfectoidRingEquiv`で既存IsIntegralPerfectoidを環同型に沿って移送。
共通側に同等の移送APIが存在しないため、BSの商比較に必要な補題としてBS内へ置いた。
`PerfectPrismQuotientPerfectoid`でF4のWitt復元と上記一般Witt商の結果を合成し、
任意の完全oriented prismの商のIsIntegralPerfectoidを証明した。
一般のpねじれ商と零環を含み、F7や引用に依存しない。
3公開定理の対象ビルド・BS専用監査が成功。公理依存は標準3公理のみ。
任意perfectoid環の逆対応・射・一般IsPerfectoidizationは未完了。

## B3-4追加：任意perfectoid試験環の商表示（2026-10-14）

`PerfectoidDistinguishedKernel`で既存Fontaine核判定を再利用し、
非零perfectoidの四条件からdistinguished核生成元を選んだ。
`PerfectDeltaPDQuotientEquiv`で、完全δ環のdistinguished商がp進完備であれば
実PD完備化前後の商が同型であることを証明。実H⁰の環普遍性を使い、
古典的完備化へ置き換えない。商のp正則性は不要。
`PerfectoidTrialPrism`で任意の非零perfectoid試験環の具体的完全prism商表示を得た。
源はWitt(tilt)、環は実PDCompletionH0、標準射とFontaine射の図式を公開した。
零試験環は最終普遍性で自明な一意射として扱う。

新規3公開定理の対象ビルド・BS専用監査と全体ビルド（4350ジョブ）成功。
公理依存は標準3公理のみ。F7・既存引用なし。
射の持上げと一般B3のIsPerfectoidizationは引き続き未完了。

## B3-4追加：商の射の一意持上げ（2026-10-14）

`WittQuotientHomFaithful`で、完全係数環のWitt射はdistinguished商への射で
決まることを証明。Perfectionの普遍性と一般tilt比較射の単射性を使う。
`WittQuotientHomLift`で、一般の完備distinguished Witt商間の環射を
唯一の標準δ射へ持ち上げた。商のp正則性は不要。
`PerfectPrismHomLift`でWitt復元を合成し、非零完全prism商間の任意の環射の
唯一のprism射への持上げを公開した。選択生成元の厳密保存は要求しない。

3公開定理の対象ビルド・BS専用監査が成功。標準3公理のみ、新規引用なし。
完全試験prismへの一意普遍性を環としてのIsPerfectoidizationへ移す準備が整った。

## B3-7：採用した一般存在・普遍性の証明経路（2026-10-14）

除算→完全化→実PD完備化の候補経路について、完全試験prismへの一意普遍性、
生成元正則性・実完備性、任意perfectoid試験環の商表示、一般の商射の唯一持上げを
すべて証明したため、一般B3の存在・普遍性の経路として採用する。
原典のδ除算・Lemma 3.9の完全化・Theorem 3.10の対応という構成要素を用い、
Corollary 7.3で必要な完全試験対象の始対象を直接構成する。
原典Prop 7.2の全prismに対する始対象を先に構成する反復順序とは異なる。

このため、当初B3-5〜6のω₁反復・一般prismの始対象・一般Lemma 4.8は、
一般B3の最終公開定理への必要条件ではなくなった。
これらを証明済みとは数えず、原典Prop 7.2自体の未実装の別工程として保持する。
この順序変更は有限生成・p正則・特殊試験環への限定ではない。

`PerfectPrismQuotientPerfectoidization`の具体的な公開射は
`perfectPrismQuotientPerfectoidizationMap P hP r hr`。
Pは完全oriented prism、r:A→Sは全射、r(P.generator)=0、
pはA/P.idealで非可逆である。J=ker(r)、
C=PerfectDeltaDivisionPrismCarrier P.deltaStructure P.generator J / (dの標準像)。
その射のIsPerfectoidizationを、任意perfectoid試験環T（零環も含む）について証明した。

`SemiperfectoidPerfectoidization`の最終入口は
`exists_perfectoidization_of_semiperfectoid_quotient hR q hq hS`。
p素数、R,S:Type u可換環、hR:IsIntegralPerfectoid R p、q:R→S全射、
hS:IsModuleComplete S (p:S) (ModuleCat.of S S)から、
∃C:Type u, ∃CommRing C, ∃f:S→C, IsPerfectoidization p fを得る。
RとSのp正則性、Sの有界ねじれ・古典的完備性・有限性を仮定しない。
零Rの場合も含む。

さらに`exists_perfectoidization_of_perfectoid_surjective_quotient`では、
同じ構成の実導来完備化を通じてSの完備性を要求しない強い存在入口を証明した。
原典入力の入口を削除せず、導来p完備性を明示した系として保持する。
全射性はこの証明に含めずB4へ分ける。
B-I/B6、André、既存B-S/B-R引用を削除・弱化せず、依存に使わない。

## 原典と依存監査

参照版は著者公開版`paper/refs/BS-prisms-author.pdf`。
Theorem 3.10（印刷p.32）、Prop 7.2（p.55）、Cor 7.3（p.56）を確認した。
全射性は著者版Theorem 7.4でありB4の別工程。arXiv v3の番号を流用しない。

最終2モジュールのプロジェクトimport閉包は182モジュール。
Inputs・CLMST・Paper・RootTower依存なし。
共有ファイル・利用先・ルートimport・共有監査は編集していない。
最終のビルド・BS専用公理監査の結果は次の完了記録に記す。

## B3完了の検証記録（2026-10-14）

最終5公開宣言（具体的射、そのIsPerfectoidization、prism商の存在、
一般perfectoid全射商の存在、導来p完備商の原典入口）は、
全BS宣言を含む`scripts/audit_bhatt_scholze.lean`でsorry-freeを確認した。
公理依存はpropext・Classical.choice・Quot.soundのみ。
最終定理を別の小さい監査でも再確認し、実際の公開署名に
一般のIsIntegralPerfectoid、全射q、Sの実導来p完備性が残ることを確認した。

最終対象ビルド3261ジョブ、全体ビルド4352ジョブが成功。
原典版・定理番号・182モジュールの依存閉包も確認した。
新しいsorry・公理・外部引用なし。既存引用に相対的な成果はこのB3の依存にない。
共有コードの変更を含めず、この工程の変更だけを個別コミットする。

一般B3の受入条件は達成した。次のBS工程はB4の全射性であり、
Andréの名前付きsorryからの途中成果を条件付きと区別する。
B-I/B6の引用と公開APIを維持する。CLMST・Serreへの接続は共通担当へ渡す。
