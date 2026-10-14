# B3一般存在・普遍性の実行計画

2026-10-14。BS主計画のB3に関する実行記録。
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
- F6・F7：共通側の実装と公開APIの受領を確認後に一般Fontaine比較へ接続する。
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
実際の反復構成の不足はProp72Construction.mdに記載した型で解消する。
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
