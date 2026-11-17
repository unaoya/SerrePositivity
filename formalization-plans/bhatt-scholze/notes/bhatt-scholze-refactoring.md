# Bhatt–Scholze 形式化のリファクタリング計画

> **既知の問題（2026-10-24 17:45、コーディネータ記録）**：`scripts/audit_bhatt_scholze_refactoring.lean:838` の `example` が
> `Ideal.Quotient.mk` の環 instance の型不一致（`AddMonoidAlgebra.ring` 経由と `Ideal.Quotient.ring` 経由の semiring 構造の不一致）で失敗する。
> 閉包は BhattScholze 配下のみで、10-23〜24 の ∞ 圏基盤リファクタとは無関係（BS のソースは基準タグ以降不変）。第 II 段の BS 再開時に修正する。


作成日：2026-10-16。改稿：2026-10-18（§1〜§12 の調査・実施記録と §13.6 は [archive/bhatt-scholze-refactoring-log.md](../../archive/bhatt-scholze-refactoring-log.md) へ移した）。
BS の証明済み構成を保ち、既存 API の再利用、一般補題の配置修正、重複証明の統合を行う。
原典の証明経路の正本は [BS 主計画](bhatt-scholze.md)。この計画は証明経路や引用範囲を変更しない。

2026-10-18 時点の注意：André（Thm 7.14）は証明済みで、`Inputs/AndreFlatness.lean` に `sorry` はない。
2026-10-25 追記：Q10 は新しい共通 API を作らず、既存の `IsPerfectoidization.precomp_ringEquiv` の適用で済ませた（BS-W1）。B4 は André 経由に改め（BR9、BS-W3）、Rooted 系列は `Semiperfectoid/RootEnvelope/` に移した。以下の記述のファイルの位置は W2・W3 前のもの。
以下の「André 条件付き監査」「André の既存引用」の記述は、条件付きの途中成果を別に監査するという意味でのみ有効である。
CLMST は完了したので、「CLMST 計画 §0.2」の担当・待合せは [archive/clmst.md](../../archive/clmst.md) の記録として扱う。

## 13 今回の実施結果を反映した次期計画（2026-10-16）

文書改訂開始時HEADは`53f9d03d`。N4・N7と最終検証の保存後を基準とする。
今回の目的は残る重複を具体的な利用先と最小契約に分け、次の実装単位を選べる状態にすること。
R1〜R6・N1〜N3・N5、共通移管7ファイルは再実装せず、回帰検査の基準として保持する。
旧N5のMilnor短縮は保存済みだが、二つのpure本文の現行形は後続N7の共通判定への適用である。
リファクタリングの全候補をB5開始の前提にはせず、担当が重ならない数学的工程と並行できる順序にする。

### 13.1 担当・並行作業・検証済みの基準

BS担当はこの計画、BS内の具体的比較、共通API受領後のBS利用先、BS専用監査を編集する。
共通CA/HA、CLMST、RootTower、DG・ホモトピー、ルートimport、共有監査は変更しない。
§12.1の移管7ファイルに加え、並行担当による`PerfectDeltaCompletedTensorDiscrete`、
`PerfectDeltaTensorRegular`、`PerfectDeltaTensorStructure`、`PerfectDeltaTensorPCompletion`と
後続の完備tensor接続系列も、BhattScholze内にあっても同時編集しない。
新しい共通APIのソース発見・担当側の検証報告・コミット済み・BSでの適用検証をそれぞれ区別する。
外部チャットへの新たな送信は、ユーザーの許可がある場合だけ行う。

再開時に欠けていた旧`compatibleRootIdealTensorMap_tmul`のBS互換名は、ユーザーの個別送信許可後に
修復案と監査エラーをCLMSTへ送り、移管担当が`e2215f2c`でaliasと旧simp属性を復旧した。BS側では当該ファイルを編集していない。
復旧後の通常B4監査は終了0。旧31名の完全性を基準にし、一時aliasや監査対象の削減は行っていない。
移管前31名の完全型・計算契約の追加照合も完了した。以前の別37宣言の型比較記録とは区別し、結果を§13.6に記す。

文書改訂時のBSは580モジュール・54,519行。これはソース棚卸しであり、新しいビルドの結果ではない。
直前のBS統合検証は536対象・4,586ジョブ、基礎584件・通常B4 2,560件・refactoring 195件が成功。
文書改訂時にも、そのimport閉包と監査を含む909ソースのhashは検証時と一致している。
構造監査の指定8基盤入口も成功済みだが、並行追加を含む共有ルート全体のビルド成功とは区別する。
André条件付き監査とB-I/B6は既存引用の境界を維持する。

### 13.2 完了した工程と採用しなかった変更

| ID | 対象・内容 | 現在の状態 |
| --- | --- | --- |
| N4確定 | DeltaDivisionEvaluationFiniteSupportColimitの共通有限和商colimitへの委譲 | 元の9公開型、図式・局所作用・標準射、空有限集合・空族・零環、下流Tor、旧新同型を検証。`c34770f7`で保存済み |
| N7 | PerfectPrismRootSourceDiscrete、PerfectPrismDeltaAlgebraDiscreteのpure本体を新しい共通離散性判定へ接続 | 旧10公開型、元の実対象、正規化single/H0比較、旧public importを保持。公開冪余核補題を削除せず、新仮定・引用なし。`86288280`で保存済み |
| N6測定 | DeltaDivisionSecondCoefficientPowerEquivの型照合時間を測定 | 宣言単位の原因を特定し、直接証明の試作まで通常設定で検証済み。安定した改善の根拠がないためコード変更は未採用 |

N4では図式・遷移・評価射を残して共通余極限定理を使えた。旧新の比較同型全体と逆射の一致まで検証できたため、
他の余極限の整理でも「公開型が同じ」だけで受け入れず、標準射と実際の同型を比較する。
残るℕ添字の二図式はQ2として別に評価する。

N7では既存のmod d還元の純性、基底のd正則性、同じXのd導来完備性から一般判定を適用できた。
全冪塔の再構成を利用先で展開する必要がなくなったため、二利用先のためのQ9新設は採用対象から外す。
既存の公開冪余核補題とsingle/H0正規化、MilnorAnnihilatorのpublic importは互換性のため保持済み。
証明本文の短縮をimport依存の除去とは数えない。

N6では`deltaDivisionSecondCoefficientPowerEquiv_mk`のカーネル検査が約126秒を占めることを特定した。
直接congrArgを使う試作でも大きな費用が残り、性能変更は不採用とした。継続測定を必須工程にはしない。
再開するなら、同じ通常設定・依存olean・並行負荷を管理したbaseline/候補の複数回測定と、
元の同型・係数/変数公式・公開型の保存を採用条件にする。heartbeat増加や一回のwall時間差だけでは採用しない。

### 13.3 共通抽出の優先順位と正確な利用先

Q群は未到着のG要求ではなく、既存証明をまとめる候補。担当調整後に共通側で実装し、BSは実入力へ適用する。
優先する三件の着手目安はQ10 → Q1 → Q8。ただし相互の数学的依存はなく、担当側の準備状況に応じて受領順を変えられる。
共通待ちの間は、後述のQ2のBS内比較を独立に試作できる。候補全部の実施を一括した完了条件にはしない。

| 優先 | 候補・配置案 | 現在の需要と最小契約 |
| --- | --- | --- |
| 高・小規模 | Q10、CA/PerfectoidizationFunctor近傍 | **3箇所**。RootedKernelSurjectivity、RootedPresentationSurjectivity、RootedIdealSurjectivity。hfと源同型eからf.comp eのIsPerfectoidization。同じC・f・universeを保ち、根・全射性・完備性は一般補題に不要。第三の利用はe.symmを渡す |
| 高 | Q1、CA/CompletelyFlatCriterion | BS5箇所。標準商射のTor消滅と、同じextendScalarsの忠実平坦性から完全忠実平坦性。正則性・FG・完備性不要。具体的作用の比較はBSに残す |
| 高 | Q8、HA/DerivedCompletion/ReflectionTransport近傍 | BSのDeltaRootRawCompletedH0Ringと、共通PrincipalCompletionDerivedComparison・CompletedAlgebraPrincipalComparisonの計3箇所。反射性h、指定済み線形同型E、E(e)=1から同じEの代数同型。終域完備性はhとEから内部導出する最小案 |
| 中・第二群の先頭 | 二段Hom同値、HA/DerivedCompletion | BS3箇所。Yのa,b導来完備性からHom(Λ_bΛ_a X,Y)≃Hom(X,Y)。実導来圏の入口ではXの完備性・正則性・上有界性不要。BSの中間p段の公開射、既存逆射の合成、合成単位、Minus包装を保持 |
| 中 | Q7、HA/DerivedCompletion/RestrictionCompletion近傍 | BS2箇所。G8の二回適用による二段係数制限比較と合成単位。実導来圏とMinusの版を区別 |
| 中・部分受領 | Q4、CA/AdicCompletionExt・AdicCompletionAlgebraUniversal近傍 | FGイデアルの古典的完備代数への代数射版は保存済み。一般環射f、I.map f≤J、FG不要の存在と、FG・J分離性による一意性は別契約として残す |
| BS独立の試作候補 | Q2、残るℕ図式2件 | 単一根版を有限族版のm=1へ比較する案と、共通の一般商colimit抽出を択一にする。旧図式・評価射を保つ比較の負担を測り、両方を順番には実施しない |
| 中低 | Q3、一般正則族 | 独立prefix証明2件。有限集合外の商上正則性からnodupリストの弱正則性。Nontrivial不要 |
| 保留 | Q5・Q6 | それぞれ導来完備性の閉性・実反復H0反射性の単一実装。所属整理を急がず、任意有限列への拡張もしない |
| 今回は不要 | Q9の新一般化 | N7で二つの利用先を既存の共通mod d判定へ接続済み。負次数だけの別利用需要が現れるまで新設しない |

**Q10・Q1・Q8の受渡し単位。** 公開名は共通担当が既存の命名に合わせて確定し、以下の型と計算契約を先に固定する。

- Q10：`[Fact p.Prime]`と同一universeの可換環について、`hf : IsPerfectoidization p f`と`e : S′ ≃+* S`から
  `IsPerfectoidization p (f.comp e.toRingHom)`。同じ終域Cと写像fを保持する。
  BS側はRootedKernel/Presentation/IdealSurjectivityの三つの普遍性展開だけを置換する。
- Q1：`hTor : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R M)`と、
  `((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of R M))`の商環上の忠実平坦性から
  `IsCompletelyFaithfullyFlat I M`。BSのPerfectPrismRootPDCompletelyFlat、PerfectPrismDeltaAlgebraPDCompletelyFlat、
  PerfectPrismRootPrismCompletelyFlat、PerfectPrismRootPerfectoidCompletelyFlat、PerfectPrismRootedPerfectoidExtensionへ適用する。
  定義中の剰余作用と元のModuleCatの作用を同じ比較で結び、一般補題に正則性を追加しない。
- Q8：`h : IsCompleteModuleReflection R a B e`と、同じuniverseのR代数Tへの
  `E : B ≃ₗ[R] T`、`E e = 1`から、hが与える環・代数構造上で`B ≃ₐ[R] T`を構成する。
  Tの完備性はReflectionTransportの既存`isModuleComplete_of_linearEquiv`にh.isCompleteとEを渡して得る方針。
  `linearMap_map_mul`と`AlgEquiv.ofLinearEquiv`を使い、順逆の関数をEとE.symmに固定する。
  独立のT完備性を省くこの型案は読み取り照合段階で、まだ実装・Lean検証済みの公開APIではない。
  BS側の旧`deltaRootRawInternalPDAlgEquiv_apply`のrflと標準単位公式を受入条件とする。

**Q4の部分受領と残る一般性。** `9c3c9742`の共通`AdicCompletionAlgebraUniversal`は、
`I.FG`、`[Algebra R A]`、`[IsAdicComplete I A]`から標準代数射・単位公式・一意性を提供する。
担当側は対象2,144ジョブと4宣言・2型検査の成功を記録している。今回BS側では再ビルド・適用していない。
元のQ4は任意fと終域イデアルJを扱い、存在にはI.FG不要、一意性にはI.FGとJ分離性で足りる。
新APIをそのまま`DeltaAdicLift`全体へ代入すると仮定が強くなるため、一般入口は保持する。
まず共通担当で旧`PerfectoidizationCompletion.completionLift`との標準単位を保つ一致を用意し、
BS側は新APIの完備性仮定を既存条件から供給できる場合の環射部分へ適用する。δ両立性と分離終域への一般一意性はBSに残す。
PerfectDeltaPCompletionへの適用は後順位とし、逆Frobenius・既存延長射を再選択しない。

**Q2のBS独立試作。** 対象は`DeltaDivisionSourceEvaluationColimit`と
`DeltaDivisionFamilySourceEvaluationColimit`の二つのIsColimit証明。
単一根の`[Unique σ]`から`Fin 1 ≃ σ`を取り、両側の既存`Ideal_eq_one`で各段イデアルを比較し、
図式と余錐の同型を通して有限族版へ委譲する案を、まず単一根版一箇所で試す。
現時点のimport調査では有限族版から単一根版への逆依存はないが、比較のLean検証は未実施。
旧図式・遷移・評価射・局所β作用・公開型を保ち、標準同型の順逆一致と下流Torを検査する。
比較層の量・検証費用が消える重複を上回る場合は不採用とし、旧証明を保ったまま一般Q2抽出へ戻す。
一般Q2を先に受領した場合もこの特殊化案は実施しない。これはBS内の具体的比較であり、汎用版の二重実装はしない。

**第二群と保留の再開条件。** 二段Hom同値はDeltaRootSourceCandidateCompletion、DeltaRootSourceCandidateFactorization、
DeltaAlgebraPerfectionPDCompletionMapの三箇所に適用する小さい抽出として優先する。
Q7は実導来圏版とMinus版を別々に検証し、合成単位とH0作用の比較まで揃った側から適用する。
Q3はDeltaDivisionFiniteJetFamilyRegularityとDeltaRootFiniteRegularSequenceの二つのprefix証明だけを対象とし、
新しいNontrivial・Noether性・p正則性を一般補題へ追加しない。
Q5はδ非依存の三補題が一箇所に実装済み、Q6も反射性の一本を既に複数箇所で共用している。
新しい共通側の利用先が生じた場合に移管を再検討し、所属の整理だけで今の作業を広げない。

### 13.4 並行数学と統合しない境界

`9aefab1c`の自由完全多項式代数の平坦性、`f504e374`の完全環の任意図式のTor独立性、
`d08d555e`の平坦性を仮定しない完備対象の純性判定、`b197c659`の完全剰余上の完備tensor離散性は保存済み。
BSで同じ一般構成・Tor証明を再実装しない。並行担当の後続成果は次の段階まで進んだ。

| 段階 | 保存済みの成果 | まだ必要な比較・条件 |
| --- | --- | --- |
| 通常tensor | `80b96cdc`のp正則性、`9d951849`の完全δ構造と標準δ射 | δ構造には両基底射のδ両立性を使う。普遍射のδ両立性には終域のp正則性を保持 |
| 古典的p完備化 | `fee1615a`の完全δ構造、元の単位と両因子・基底の標準δ射 | 元の実導来p完備tensorのH0との、標準単位と両因子の射を保つ環同型 |
| 古典的完備化の普遍性 | `9c3c9742`のFGイデアルについての完備代数への延長 | 実主元完備化H0との比較、対象の正則性・完備性と元の作用の供給 |

これらは並行担当の保存・検証記録を受領した状態で、今回のBSリファクタリングで新たに証明した成果ではない。
古典的p完備化のδ構造を得たことだけで、実H0上のδ構造移送を完了とはしない。
後段d完備化、prismのCartier条件、標準商とperfectoid完備tensorの比較、B5の実乗法hμは別の数学である。
CompletedQuotientTensorExtensionのhμからmod pⁿ冪等性への含意は再利用し、H0同型だけでhμの完成とはしない。
CLMSTの具体的試験加群のTor入力、J²零化から必要なJ零化への入力、B-I/B6・Andréの引用境界も維持する。

RootTowerは一般余極限平坦性を使えても、各段上のcofinal tail・明示基底・階数・冪遷移を残す。
DGの非有界K-flat性・相対tensor作用・全Hom自然性、ホモトピーの実resolution/bar比較は、BSの標準Tor・上有界導来対象と統合しない。
K理論のNoether性・有限支持・perfect性をBSの一般環上の定理へ持ち込まない。具体的な二重実装が確認できた場合だけ共有候補にする。
CA/PerfectoidIdealのようなB3を消費する接続層を、BS非依存の純基盤と混同しない。

### 13.5 検証・文書・保存

次の実装は以下の小さい単位で選ぶ。今回の文書改訂はその計画の提示までとする。

1. **契約を固定する。** 対象の担当、旧公開名・完全型・標準射・属性、ソース状態を記録する。
   共通API候補は新規G要求と混同せず、実装前に担当と予定配置を調整する。
2. **BS内比較を一案だけ評価する。** Q2特殊化を選ぶ場合は単一根側の比較・委譲・回帰検査で一単位とする。
   比較が重くなる、または共通Q2が先に届く場合は不採用を記録し、既存コードを維持する。
3. **Q10・Q1・Q8を順次受領する。** 共通担当の追加とBS側の適用を別コミットにする。
   共通三件の完成を一括して待たず、公開型・計算契約・検証が揃ったものから、その利用先だけを置換する。
4. **第二群を選ぶ。** 二段Hom、Q7、Q4の限定された適用、Q3の順を目安に、需要と比較費用で採否を決める。
   Q4の広い一般性の移管は、到着した代数射版への接続と別工程にする。
5. **各単位で検証・保存する。** 通常設定の対象・下流ビルド、完全型、必要なrfl/rw/simp、標準射の式、
   assert_no_sorry・公理依存を確認する。宇宙・局所作用、空族・零環・pねじれの一般性を保持する。
   IsColimitや同型の変更では、型だけでなく元の標準同型との一致を証明する。
6. **区切りで統合する。** 基礎・通常B4・refactoringとAndré条件付き監査を分け、BSの対象閉包をビルドする。
   旧名の完全性は移管後の列挙だけに依存せず、移管前の公開一覧を基準にする。
   引用非依存、既存引用に相対的、未実装の三状態を分けて文書へ反映する。

新しいsorry・公理・引用を追加せず、新しい型クラスやchoiceによって既存契約を隠さない。
ソースhashと実行の終了結果を記録し、並行変更を別扱いにする。対象ソースが変わらない文書改訂だけなら、
前回検証を明示して用い、新しいLeanビルド成功として数えない。
共有監査の旧表示や許可リストは共通担当が更新し、名前到達と実際のsorryAx依存を区別する。
現在地は§13に集約して更新し、履歴のためだけの新節を毎回追加しない。
自分の検証済みファイルだけをパス指定でコミットし、他担当の差分・ステージ内容を含めない。

