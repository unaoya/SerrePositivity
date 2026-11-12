# §5・§6 HT 比較と結晶比較、de Rham 比較：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。§2〜§4 と同じ形。**扱いは調整役が判断する。** 事実に推奨を添える。

- 基準：main 1fe94b85d 前後。読み取りだけのエージェントがノートの加筆 2 本、コードの見直し 1 本（件数を含む）。件数のスクリプトはノートのチャットの作業用の場所にある。規模の見立ては推測。
- 原典の項目は Not 5.1、Thm 5.2、Rem 5.3、Lemma 5.4、Cor 5.5、Construction 6.1、Prop 6.2、Thm 6.3、Thm 6.4 の 9 つ。
- 二種類の提案：**A. リファクタ（R5-1〜R5-7）**、**B. 形式化の計画（§3 の表と §3.1 の計画上の点）**。

## 0. 規模と中身の分かれ方（確認済み）

- 対象は 241 本・31,781 行：Prismatic/ 直下 233 本（Crystalline* 86、PD* 113、Witt* 22、ほか 12 本）と Prism/Basic の Construction 6.1 の 8 本。**本体に sorry は 0。**
- import の錐で分けると五つ：(a) D68 の経路（`hodgeTate_of_deRham_cartier` の錐）76 本・11,512 行、(b) 結晶 site の古典部分 30 本・2,499 行、(c) Construction 6.1 10 本・1,279 行、(d) Thm 6.4（D69 の zigzag の古典部分）116 本、(e) Berthelot の一般の分冪包 9 本（BS を import しない、Mathlib と CommutativeAlgebra だけ）。
- 原典の項目番号を docstring に一つも引かないファイルが 128/241 本。Thm 6.4 を引く 85 本のうち 61 本は名前が Crystalline*・PD* で、B3 の仮の仕分けでは「Crystalline 204」に入る。
- 本体にある主な定理（すべて特別な場合）：Lemma 5.4 は `frobeniusTwist_cech_quasiIso_infinite`（FrobeniusCechComparison:472、N は余単体的可換環、変数は任意）。Thm 5.2 の \((\mathbb Z_p,(p))\)・\(\mathbb F_p[X]\) の場合は mod p が `crystallineBridgeModP_isCohomologyIso`（CrystallineBridgePushout:150）、整係数が `crystallineSmallBridgeCochainMap_quasiIso`（CrystallineSmallBridgeQuasiIso:125）。W(C) と pd イデアル J の場合（Thm 6.4 で使う形）が `wittBigCompletedBridge_quasiIso`（WittBigCompletedBridge:95）。Cor 5.5 の \((\mathbb Z_p,(p))\) の場合が `hodgeTate_of_deRham_cartier`（HodgeTateCartierAssembly:180）。Construction 6.1 (1)(2) は鎖複体版（保存性 Construction61Reflection:36、検出 Construction61Detection:46、Tor 振幅 3 は CrystallineCoverCompleteTor:39）。結晶 site は本質的な小ささ（CrystallineSiteSmall:92）、\(\mathcal O_{\mathrm{crys}}\) の層条件（CrystallineSmallStructureSheaf:64）、pro 弱終性（CrystallineCechCutoff:62）、Poincaré の複体の段（CrystallinePolynomialSpan:60）。
- **Thm 6.4 の古典部分は普遍 prism より一般の P で述べてある**（WittBigCompletedBridge:46–51 の仮定：\(A\) と \(A/d\) が p ねじれなし、p と素な整数が \(A/d\) で単元、\(A/d\) が p 進完備、P は有界）。\(A_0\) に特殊化する UniversalWittComparison:55・62 の 5 宣言は未使用。
- 本体の `HodgeTateIsoStatement`（HodgeTateCompletedMap:461）は古典的な主張（Čech–Alexander 模型の複体からの写像が全次数で全単射）。

## 1. A. リファクタの提案（今あるコードを直す）

### R5-1 drafts/A1 の古典部分は本体に置き換わっている【推奨：5∞-0。R4-1 を A1 の残り 3 本に広げる】

| drafts | 宣言 | sorry を含む | 本体と同名 | 本体と同名の例 |
| --- | --- | --- | --- | --- |
| CrystallineInput | 40 | 23 | 11 | `pdCechNerve`:244、`pdCechNerveMap_quasiIso`:288、`exists_completedPDEnvelope`:222、`pdModel_iso_pdCechNerve`:303 など（本体は PDCechNerve、PDCechFrameHomotopy:326、CompletedPDEnvelope:158、PDSmallModelComparison:242） |
| CrystallineSite | 51 | 30 | 22 | `CrysOver`、`zariskiTopology`、`crystallineStructure_isSheaf`:305、`pdCechTower_proWeaklyTerminal`:464、`essentiallySmall`:253 など |
| DeRhamComparisonPoly | 76 | 47 | 23 | `wittBigCrystalline`、`wittBigBridge`、`wittToSmall`、`wittSmallFrame`、`wZero_isDPMorphism`、`bigCechAlexander` など |
| HodgeTateComparison | 60 | 20 | 14 | うち 7 は既に本体を指す abbrev |
| HodgeTateMap | 5 | 1 | 0 | — |

- drafts の側の多くは sorry のまま。本体の版は一般の P で、drafts の版は \(A_0\) への特殊化のことがある。CrystallineInput は D68 の分だけ「本体の … に置く」に書き換え済み（:140–146・:396–472）で、D69 の分と module docstring の「段は六つ」は古い。CrystallineSite と DeRhamComparisonPoly は未着手。5 本とも冒頭が「基準コミット 972bb7f53」のまま。
- R4-1 の表に入っているのは HodgeTateMap・HodgeTateComparison の一部だけ。5∞-0 の対象に CrystallineInput の D69 の分、CrystallineSite、DeRhamComparisonPoly を足すのがよい。

### R5-2 Prop 6.2 (a)(b) の二つの sorry は Thm 6.3 の系にできる【推奨：5∞-0 か 5∞-3 の最初】

- drafts の `hodgeTate_iso`:350 の筋（D30 の (c)：\(\hat b^*\)・\(\hat c^*\) で \((\mathbb Z_p,(p))\) へ）は、`hodgeTate_iso_crystalline`:62（Cor 5.5 の一般の結晶 prism）も `hodgeTate_iso_of_construction61`:262（Prop 6.2 (b)）も使わない。結晶 prism は `crystallineBounded`（CrystallineBase:91）で有界なので、二つとも `hodgeTate_iso` の一行の系にできる（推測）。証明の要る sorry が二つ減る。原典は Cor 5.5 から Prop 6.2 (b) を経るので、順序の違いとして記録する（定理は同じ）。

### R5-3 層の向き・置き場所【推奨：B3】

- (a) **§6 から §8 への import**（台帳にない）：`CrystallineWittCoefficients:3` が `Perfectoidization.Derived.ArcPerfectoidBase` を import し、使うのは `arcPadicIntMap`・`arcPadicIntMap_unique`（ArcPerfectoidBase:406・415）だけ（CrystallineWittCoefficients:52–59）。中身は「導来 p 完備な離散環への標準の \(\mathbb Z_p\) 作用とその一意性」という一般の補題。`HomologicalAlgebra/DerivedCompletion` へ移す。
- (b) **§4 の名前のファイルが §5 のファイルに依存**：§4 の 4 本（CechVertexHomotopy:5（`import all`）、PrismaticFrameHomotopy、CompletedCechCoefficientMap、CechFrameAdditiveQuasiIso）が `PDCechFrameHomotopy` を import し、使うのは汎用の部品だけ（基底の下の可換環を加群に送る関手 `PDCechNerve.algebraModule`（PDCechFrameHomotopy:38、15 本が使う）、`cochainHomotopy`:255、添字の補題 `val_succAbove`・`val_predAbove`（CechVertexHomotopy:34））。`HomologicalAlgebra/Cosimplicial/Algebra`（`toModules`:43 の隣）へ移す。
- (c) **§4 の名前で中身が §6.4 のファイル**：AffineCechPointwiseCoefficients、AffineEnvelopePointwiseCoefficients、CechFrameAdditiveQuasiIso、CompletedCechCoefficientMap、PolynomialCompletionResidue の 5 本（docstring が引くのは Thm 6.4 だけ。PolynomialCompletionResidue は BigPDModel・CrystallinePrincipalResidue・CrystallineReductionPushout を、BigCechDerivedBaseChange・AffineEnvelopePointwiseCoefficients は CrystallineCompletedTensor を、AffineEnvelopeDerivedBaseChange は WittAffineBaseChange を import）。B3 では CechAlexander でなく §6.4 の側へ。
- (d) **B3 の「Crystalline 204」は §5 だけの束ではない**。§0 の (a)〜(e) で分け直す案：`Crystalline/{Comparison,Site}` に (a)・(b)、`DeRham/`（または HodgeTate/Comparison/Witt）に (d)、`HodgeTate/Comparison/CrystallineCover` に (c)（B3 の案のとおり）、`CommutativeAlgebra/DividedPowers/` に (e)（RelativePDEnvelope、CompletedPDEnvelope、PDAdicCompletion、PDLocalization* 4 本、PDFromGenerators、PDEnvelopeCardinality。§2 の R2-7 の FreeDP* と同じ行き先）。
- (e) **名前空間**：241 本のうち 63 本が `…Prismatic` 以外。Prism/Basic の 8 本は `…Prismatic.Construction61`（B3 の移動で解消）。ファイル名の名前空間（`…Prismatic.PDRawPolynomialSubstitution` を 13 本が共有、`WittToSmall` など）、`_root_.…wittBigCrystalline` のような書き方。

### R5-4 二重の構成【推奨：保守。(d) は台帳に新しく足す】

- (a) `hodgeTate_iso_polynomial_Zp`（:212）は `hodgeTate_of_deRham_cartier` の別名（R4-5 (a) で既出、変化なし）。
- (b) `frobeniusTwist_cech_quasiIso`（:485、有限変数）は無限変数版を当てるだけの包みで、外の利用者 0。
- (c) pd 模型が複数あり、比較の定理で結ぶ：小さい模型 `pdModel`（PDPolynomialCech・PDCompletedCech）、枠の `pdCechNerve`（PDCechNerve）、PDSmallRawEnvelope・PDPolynomialSplitEnvelope、比較 `pdModel_iso_pdCechNerve`・`pdCechNerveMap_quasiIso`。橋も二つ（原典の η（δ 座標つき、CrystallineBridge:153）と小さい橋（δ 座標を落とす））。D68 と D69 の両方が使うので残す。
- (d) **導来 Nakayama の二つのファイル**：`HomologicalAlgebra/DerivedCompletion/CompleteCochainReduction` と `HomologicalAlgebra/CochainCompleteDetection`。BS-D69 の報告（report-codex-d69.md:509・797）が統合の候補として「KL-W1 の後の別作業」に残し、台帳にない。
- (e) 同じ短い名前で型が違う：drafts の `torAmplitude_modP_le_one`:219・`crystallineCoverMap_torAmplitude`:227・`_finiteTorAmplitude`:236（∞ の型）と、本体の `Construction61.*`（CrystallineCoverFactorization:125、CrystallineCoverCompleteTor:39・66、鎖複体の型）。BR40 の Tor 振幅の一本化で名前も整理する。

### R5-5 docstring の工程ラベル【推奨：B3 の docstring の回、BR25】

- 49 行・22 ファイル：D77 19 行・8 ファイル（Construction 6.1 の群）、K1・K2（BS-W15 の段）8 行・4 ファイルと 9 行・6 ファイル、D4-04 2 行（CrystallineCoverCompleteTor:19・37）、D68 2 行（PDSmallModelComparison:16・19）、D69 5 行・5 ファイル、P1・P2 1 行（CrystallinePolynomialSpan:19）、「検収」3 ファイル（WittBigCompletedBridge:37 ほか）。「第二比較」「二つ目の Witt 比較」（5 ファイル）は設計の中だけの呼び名なので、数学の言葉（「Witt 係数から小さい模型への比較」など）に直す。
- ノートを引く記述、drafts を指す記述、「（旧 …）」は 0 件。

### R5-6 主定理の閉包・葉・未使用の宣言【推奨：消さない（R3-7・§4 の追記と同じ）】

- 主定理の閉包に入るのは 241 本のうち 0 本（閉包の BS は 103 本で Prismatic は 0）。
- 葉（集約と stage2 監査以外に importer がない）19 本：CrystallineCoverCompleteTor、Construction61Reflection、CrystallineCechCutoff、CrystallinePolynomialSpan、CrystallineSmallCoverMaps、CrystallineStructurePullback、CrystallineWittCompletedModules、CrystallineWittFlatCochain、HodgeTateCartierAssembly、PDCechFrameSiteMap、PDColumnCoefficientUnit、PDDeRhamBicomplexCoefficients、PDDeRhamCompletedBaseChange、PDDeRhamSubstitutionFunctor、PDExtraCoordinatesRetraction、PDTermCompletelyFlat、UniversalWittComparison、WittBigCompletedBridge、WittPDCompletedDerivedModel（うち 2 本は drafts/A1 からも import）。
- 公開の宣言 875 件のうち、自分のファイルの外で本体・drafts・scripts のどこにも出ないもの 243 件（自分のファイルでも未使用 78 件）。群ごと（ファイル／宣言／未使用）：D68 76／232／27、site 30／109／45、6.1 10／64／28、D69 116／420／137、Berthelot 9／50／6。全部未使用のファイル：WittPDCompletedDerivedModel 14/14、PDDeRhamSubstitutionFunctor 7/7、Construction61Reflection 4/4、UniversalWittComparison 5/5 など。本体の利用者がなく drafts にだけ同じ名前がある宣言 13 件（`crystallineCover`、`crysResidueAlgebra`、`exists_completedPDEnvelope`、`wZero_psi` など）。
- 未使用が多いのは、∞ の組み立て（Thm 6.4 の関手同型、RΓ_crys、Prop 6.2）が drafts にあり、その入力がまだ使われていないため。原典の項目の主張（`crystallineStructure_isSheaf`、`pdCechTower_proWeaklyTerminal`、`wittBigCompletedBridge_quasiIso` など）は残す。

### R5-7 設計書・地図の古い記述【推奨：調整役が直す】

- `stage-ii-second-half.md:53`：5∞-3 は「D68 の置き換え（恒久引用 1）」と書くが、D68 の恒久の引用（`crystalline_deRham_polynomial_Zp`）は 11-05 に外され（a1-design §10.2）、\((\mathbb Z_p,(p))\) の Cor 5.5 は本体で証明済み（HodgeTateCartierAssembly:180）。5∞-3 に残る中身は「Thm 6.3 の一般の有界向き付き基底と Cor 4.12」。
- `a1-design.md:44`：Prop 6.2 の名前が `hodgeTate_iso_of_crystallineCover`（drafts の実名は `hodgeTate_iso_of_construction61`）。`a1-design.md:168`：G-A1-12（普遍向き付き prism）が「未」のまま（Ex 3.4 は本体で証明済み）。a1-design §2.4 の Construction 6.1 の仮定は原典の「Frobenius が平坦」のままなので、D77（design-status:49）を参照する一行を足す。
- 地図 items.csv の 5.2・6.4 の宣言の漏れは 11-12 夜にノートの側で直した。

## 2. 台帳の項目の今の状態（§5・§6 に関わるもの）

- **BR40**：変化なし（`Construction61Hypotheses`（drafts:163）、Tor 振幅の三つの定義）。R5-4 (e) の名前の重なりを足すとよい。
- **BR41**：変化なし（`FrobeniusDivisionPD:6` が `Prismatic.CrystallineTensorRegularity` を import、使うのは 4 宣言。CrystallineTensorRegularity は Delta と CommutativeAlgebra しか import しないので、ファイルごと Delta へ移せば解ける、R2-1）。
- **BR37**：変化なし。**BR47・R3-2**：変化なし（Prism/Basic/CrystallineCover が `Prismatic.PrismOver` を、Construction61Frobenius:5 が `Andre.PowerRootEnvelope.VarpiPD` を import）。**R4-5 (a)・R4-6**：変化なし。
- **design-status:47 の後回し**（一般の I の η の 3 項目）：変化なし（report-codex-d69.md:788–796）。
- 台帳にない新しい事実：R5-1 の drafts/A1 の 3 本、R5-2、R5-3 (a)〜(c)、R5-4 (d)・(e)、R5-7。

## 3. B. 形式化の計画の提案（新しく形式化する項目）

| 項目 | 今あるもの・要るもの | 規模 | 依存 | 推奨 |
| --- | --- | --- | --- | --- |
| Not 5.1（一般の結晶 prism と pd イデアル \(I\ni p\)、ψ、\(R^{(1)}\)） | 結晶 prism は `OrientedPrism.crystalline`（Ex 3.3、本体）。pd 基底 \((k,J,\gamma)\) は結晶 site の対象（CrystallineSiteBasic:41）。ψ と \(R^{(1)}\) は本体にも drafts にもない | 小 | — | 後回し（一般の Thm 5.2 と一緒に） |
| Thm 5.2（一般の結晶 prism、pd イデアル \(I\)、smooth \(R\)、E∞、Frobenius との両立） | 本体は \((\mathbb Z_p,(p))\)・\(\mathbb F_p[X]\) の模型の上で mod p と整係数、W(C)・J の多項式、site の古典部分。不足は (i) \(R\Gamma_{\mathrm{crys}}\)（drafts の `crystallineCohomology`:313、∞ 層 S1〜S8 と pro 版の S3、CAlg 値）、(ii) 一般の \(I\) の η（design-status:47 の 3 項目）、(iii) smooth な \(R\)（Lemma 4.21、形式スキーム）、(iv) Frobenius との両立 | (i) 中、(ii) 中、(iii) 大、(iv) 中 | (i) 5∞-1 | (i)(ii) 後回し（補完。`crystallineCohomology` は drafts の CrystallineSite と README にしか出ず、Thm 6.4 の組み立ても使わない、E3 の経路の外）。(iii)(iv) 入れない |
| Rem 5.3 | Thm 5.2 と Cor 4.12 の言い換え | — | — | 入れない |
| Lemma 5.4（一般の余単体的 \(B^{\bullet,(1)}\) 加群 \(N\)） | 本体は \(N\) が余単体的可換環で ι を通す押し出しの形、変数は任意（:472）。加群版は余単体的加群のテンソル \(N\otimes_{B^{(1)}}B\) の基盤が要る。収縮の議論はそのまま通る見込み（推測） | 小〜中 | — | 後回し（補完。E3 の経路の利用者はすべて環の場合） |
| Cor 5.5（一般の結晶 prism の多項式） | drafts の `hodgeTate_iso_crystalline`:62（sorry）。R5-2 のとおり Thm 6.3 の系 | 小 | 5∞-3 | 入れる（系として、5∞-3）。後半の「p 完備底変換と可換」は Cor 4.12 の特別な場合で 5∞-3 |
| Cor 5.5（smooth な \(S\)） | Lemma 4.21 | 大 | — | 入れない |
| Construction 6.1 (1)(2) | 本体は鎖複体版（Reflection:36、Detection:46、CompleteTor:39 の上界 3）と D77 の入力。drafts は ∞ の型（`crystallineCoverMap_conservative`:199 ほか）で、橋渡しに完備反射 `moduleReflection`（sorry）と DerivedGeneral が要る | 小〜中（橋渡しだけ） | 3b-2（∞ の型を残す場合） | 入れる。ただし §3.1 の 2 の古典の経路を採るなら ∞ の型は要らない |
| Construction 6.1 (3)（Lemma 4.20） | drafts の `crystallineCoverMap_prismaticCohomology`:247 | — | 5∞-2 | 計画済み |
| Prop 6.2（一般の有界向き付き基底、一般の r） | drafts の `affineLine_moduleComparison`:344、`hodgeTate_iso`:350。要るもの：η を D(R) で選ぶこと（G-A1-10、\(\Omega^i\) は自由）、\(\hat b^*\)・\(\hat c^*\)（D30）、項ごとの一致（本体の AffineCechPrismBaseChange・AffineEnvelopeDerivedBaseChange）、Lemma 4.22、生成元での照合 | 中〜大（1〜3 千行） | Lemma 4.22、Construction 6.1 | 入れる（5∞-3）。原典の最後の段落（向き付けのない基底、Lemma 3.7(4)）は入れない（D19） |
| Thm 6.3 | 多項式の場合は Prop 6.2 の一般の r（D29）。étale 局所化は入れない | Prop 6.2 に含む | 同上 | 入れる（5∞-3）。site の RΓ との一致は 5∞-2・D27 |
| Thm 6.4（D69、関手としての同型 `deRham_iso_polynomial_universal`） | 古典の zigzag は本体（一般の P、§0）。drafts に残るもの：`bigZigzagIso`:356、`polyUnderlying_iso_bigCech`:145、`baseChangeTotHomotopy` 系、`transferWittComparison`:424、`deRham_iso_polynomial_modP`:432、`deRham_iso_rootAlgebra_modP`:494 | 中〜大 | 3b-4（CAlg 値の Tot）、5∞-2、5∞-4、5∞-3 | 入れる。ただし段の表に置き場所がない（§3.1 の 1） |
| Thm 6.4（原典の形、\(A/I\) が p ねじれなしの一般の基底） | 本体の古典部分の仮定は既にこの範囲。∞ の組み立ては普遍 prism の場合と同じ | 小（D69 の後の追加） | D69 | 後回し（補完。D69 の後なら安い、推測） |

### 3.1 計画の上で気づいた点

1. **Thm 6.4（D69）の ∞ の組み立てに段がない**（確認済み）：段の表で 5∞-3 は「HT 比較」だけ、5∞-6（A5）は 5∞-4 と 5a-9 にしか依らない。一方 drafts の依存は、`psiBaseChange`:99・`universalDeltaChange`:415 が Cor 4.12（5∞-3）、`universalTwist`:92・`polyUnderlying_iso_bigCech`:145 が A2 の `polyUnderlying`・`polyDeltaData`（5∞-4）と A0 の CAlg 値の Tot（5∞-2）、`totEInfinityFunctor` が 3b-4。使う側は A5 StrongDescent（Lemma 8.6、5∞-6）。**推奨：「5∞-4 と 5∞-3 の後、5∞-6 の前」に D69 の組み立ての段を明示する。**
2. **5∞-3 を古典の段と ∞ の段に分けられる見込み**（推測）：Prop 6.2・Thm 6.3 の主張（`HodgeTateIsoStatement`）は古典的で、入力の保存性・Tor 振幅・項ごとの底変換も本体では鎖複体版。残る基盤は Lemma 4.22 の鎖複体版（明示の複体の完備底変換を項ごとに計算する。有限 Tor 振幅のもとで上に有界でない複体を扱う）と G-A1-10。そうすると 5∞-3a（古典：Prop 6.2・Thm 6.3・Cor 5.5 の系）は 3b-2・3b-4 を待たずに開け、5∞-3b（Cor 4.12 の CAlg 値、D27 の結び）だけが ∞ の後になる。段の表の最長の経路（3b-2 → 5∞-3 → 5∞-4）が短くなる可能性がある。確かめること：drafts の `HasFiniteCompleteTorAmplitude`・`baseChangeB`・`affineModuleDiagram` の ∞ の型を捨て、古典の型に置き換えてよいか（D30 の読み替えは古典の型でも同じ）。
3. **5∞-0 に足すもの**（§5・§6 の分）：R5-1（drafts/A1 の 3 本を本体の宣言を指す形に）、R5-2（二つの sorry を系に）、BR40（Tor 振幅の定義と名前の重なり）、R5-7（設計書の訂正）。どれも数学の主張は増えない。

## 4. ノートの側（参考）

1. ノート 05 章：§5・§6 の全 9 項目を見出しと主張・Lean・証明の囲みにした（番号は §5 を 5.1.n、§6 を 5.2.n）。章末の項目の表と D 表は外し、D68・D25 を Thm 5.2、D77 を Construction 6.1、D69 を Thm 6.4、D27 を Thm 6.3 の下に移した。冒頭の「方針（10-25）」「E3 に要る範囲」の囲みは設計の決定と範囲の記録なので外し、a1-design への参照にした。
2. D68・D25・D77 の評価の「どちらが簡単か」は、旧い D 表で「—」だったので、加筆の担当が書き入れた（D68：紙の上では原典、形式化では Lean。D25：同程度。D77：Lean の方が簡単）。D 番号の決定はユーザーのものなので、違えば直す。
3. 原典の誤植と判断した所：Lemma 5.4 の証明の式 (3) の添字（\(s\in M\) は \(s\in S\)）。
4. §7 で拾うもの：`prismaticCohomology_lci_universal`（drafts/A1/DeRhamComparisonPoly.lean:505）は Ex 7.9 の特殊化なので、05 章からは外した。
5. 地図 items.csv：5.1・5.2・5.4・6.4 を直した。
