# D：coherent bar の変形 retract（工程 A）

## 引き継ぎ（2026-10-25）
### 現在地
- ユーザーの次割り当てで再開。所有は Derived/CoherentBar/Retract/ と All・専用監査のみ。
- D-bar の実 bar・正規化模型・射影・安定自己写像・全作用鎖ホモトピーを読み取り専用で使う。
- 専用 All ビルド成功（3666 jobs）・専用公理監査成功（13 葉153宣言、標準三公理のみ）。
- 修正包含の一般降下、実射影の次数成分と次数付き切断、安定自己写像が実射影を保つ式を対象検証済み。
- 面・退化の BasedOperators と合成則、前側 prefix の全高次係数一致、tail の厳密退化式、prefix 後の退化単位の合成消去を対象検証済み。
- BasedCoproduct は未シフト係数直和と始点保存写像の作用・恒等則まで。合成則の試作は elaboration 上限で未検証（/tmp/d-retract-basedcoproduct-composition-draft.lean）。
- CorrectedInclusion は退化因子消去を明示仮定とする補助入口。無条件の retract は未完。
### 残り（依存順）
- 1. 安定作用素の退化因子消去：全 prefix の相殺、始点を保つラベル正規化との照合。
- 2. 修正包含の閉性・包含後射影の恒等・射影後包含の全作用鎖ホモトピーへ無条件代入。
- 3. 自分の集約・専用監査、限定コミット、公開名の報告と停止。
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
### 未コミット
- 検証済みの基礎・係数葉と All・専用監査を限定コミットで保存。無条件の退化消去は未供給。
### 既知の問題
- 安定自己写像が恒等にホモトピックで射影を保つことだけでは因子化は導けない。
- 補助入口の退化消去仮定を無条件に解消するまで工程 A の完了とはしない。
### 次の一手
- PrefixDegeneracyComposition の前側合成式と PrefixVanishing の後側消滅を合わせ、ホモトピー後の prefix との符号相殺を示す。続いて面項とラベル PInfty の照合で DGCoherentBarNormalizationKillsDegenerate を無条件に証明する。

## 運用
- 新規 sorry・公理・引用なし。ModelCategory SSet の instance を主経路に置かない。
- 新規葉のみ。既存宣言・既存モジュールは不変。移動・改名・削除はしない。
- All のビルド終端後に専用監査。根のビルド・.lake の削除はしない。
- set -o pipefail のうえ所有パスのみ git commit --only。
- 実施記録はコミット本文。完成後は公開名を報告して停止する。
