# D：coherent bar の変形 retract（工程 A）

## 引き継ぎ（2026-10-25）
### 現在地
- チャット稼働の基準は 2026-10-25 18:07 頃。24 時間の期限は 10-26 18:07 頃（新割り当てでリセットしない）。
- ユーザーの次割り当てで再開。所有は Derived/CoherentBar/Retract/ と All・専用監査のみ。
- D-bar の実 bar・正規化模型・射影・安定自己写像・全作用鎖ホモトピーを読み取り専用で使う。
- 専用 All ビルド成功（3708 jobs）・専用公理監査成功（35 葉311宣言、標準三公理のみ）。
- 修正包含の一般降下、実射影の次数成分と次数付き切断、安定自己写像が実射影を保つ式を対象検証済み。
- 面・退化の BasedOperators と合成則、前側 prefix の全高次係数一致、tail の厳密退化式、prefix 後の退化単位の合成消去を対象検証済み。
- BasedCoproduct の合成則は BasedCoproductComposition で三つの対象輸送を明示して対象検証済み。旧 timeout 試作は /tmp/d-retract-basedcoproduct-composition-draft.lean に保持。
- PrefixHomotopyAction でホモトピー後の prefix を切断後の退化列へ制限する全 Hom の式を対象検証済み。
- PrefixBlockInterchange・PrefixTermInterchange で退化前後の prefix 合成が全 Hom で一致。PrefixSums は正位置の有限和を相殺、PrefixAtZero は零位置の残余単位項と面を同定（対象検証済み）。
- UniversalLabelCoefficients・UniversalLabelNaturality は標準単体の普遍正規化係数・始点支持・退化押出し零。BasedCoefficientAction・BasedUniversalCoefficients は始点保存の部分型に制限し、未シフト係数直和作用での退化消滅まで対象検証済み。
- BoundaryFaceTerms・BoundaryExpansion は theta/H と元の列との二合成を展開。BoundaryFacesOnly.dgCoherentBarNormalizationBoundary_restrict_faces は正位置（q < n+1）の実境界を面和だけで計算する（対象検証済み）。
- FaceHomotopyAction は面の後の H の作用と次数消滅。LastBoundaryParts・LastBoundaryFacesOnly は最後の段（q = 単体次数）の単位面・prefix の相殺と残る面和、VertexBoundary は次数零の境界消滅を対象検証済み。
- CorrectedInclusion は退化因子消去を明示仮定とする補助入口。無条件の retract は未完。
### 残り（依存順）
- 1. 安定作用素の退化因子消去：全 prefix の相殺、始点を保つラベル正規化との照合。
- 2. 修正包含の閉性・包含後射影の恒等・射影後包含の全作用鎖ホモトピーへ無条件代入。
- 3. 自分の集約・専用監査、限定コミット、工程 A の公開名を報告。
- 4. 工程 A の完了後、CoherentBar/Compact/ の新規葉・All・専用監査で c2・c6・c7 へ（次のユーザー割り当て）。
### 主要宣言
- dgBarRetract_correctedSection・dgBarRetract_projection_correctedSection。
- dgBarRetract_correctedSection_projection。
- dgCoherentBarNormalizedModuleProjection_evaluation_f。
- dgCoherentBarNormalizedGradedSection_projection・_naturality。
- dgCoherentBarNormalizationEndomorphism_evaluation_f・_projection。
- DGCoherentBarNormalizationKillsDegenerate（残る係数検証の正確な型）。
- dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish。
- dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish。
### 依存と提供
- D-bar の既存 CoherentBar/ は編集しない。D-e の KappaCovers/・KappaPerfect/ も編集しない。
- Mathlib DoldKan の PInfty・homotopyPInftyToId・退化消滅を直接使用できる。
- D-bar へ同じ正規化実加群・同じ閉射影による変形 retract を提供する。
### 保存範囲
- 検証済みの35葉と All・専用監査を限定コミットで保存。無条件の退化消去は未供給。
### 既知の問題
- 安定自己写像が恒等にホモトピックで射影を保つことだけでは因子化は導けない。
- 補助入口の退化消去仮定を無条件に解消するまで工程 A の完了とはしない。
### 次の一手
- BoundaryFacesOnly・LastBoundaryFacesOnly・VertexBoundary の実境界の面式を始点保存作用へ戻し、実段階作用素と普遍 P/PInfty を照合する。BasedUniversalCoefficients の退化消滅から DGCoherentBarNormalizationKillsDegenerate を無条件に証明する。

## 運用
- 新規 sorry・公理・引用なし。ModelCategory SSet の instance を主経路に置かない。
- 新規葉のみ。既存宣言・既存モジュールは不変。移動・改名・削除はしない。
- All のビルド終端後に専用監査。根のビルド・.lake の削除はしない。
- set -o pipefail のうえ所有パスのみ git commit --only。
- 実施記録はコミット本文。工程 A 完成後は公開名を報告し、追加割り当ての Compact へ進む。

## 工程 A 後の割り当て（ユーザー判断）
- 所有：Derived/CoherentBar/Compact/ の新規葉・集約・専用監査。
- c2 の仮定は coherent な全 native κ-filtered 図式についての比較（D-e が C1 を再定式化、公開型は中継待ち）。strict 比較・poset 制限では代用しない。
- c2：Yoneda と評価の交換、coherent 比較を通じた余極限の計算から、representable・全シフト・κ未満 sphere-free 基底の native IsKappaCompact。
- c6・c7：DGKappaClosedCompactGeneratorCriterion を通じ、dgKappaClosedProjectiveObjects_property の七入力へ接続。
- 比較の実値が D-e から届いたら代入の系を追加し DGKappaConeInput の実例を構成する。
- D-bar の c2・c6・c7 は D に移管。工程 A 完了前には Compact 本体へ着手しない。
