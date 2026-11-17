# Sp-2b — d3c・d3d 先行構成

更新：2026-10-28。Sp-2 の d3b B から分割。本文 ≤200 行。

## R 窓前の停止・再開入口
- 現在地：`bdb5f0ebc` 系の条件付き d3c・d3d を保存・検証済み。
  `nativeLoop_isQCatEquivalence_of_tailComparison hB` と `sp_isStable hB` を公開。
  無条件版は未公開。先行版の検証結果は末尾の「検証」節。
- 待っている供給：Sp-2 の B の実値（refined 関手との全 Hom 比較）と公開名。
  `NativeLoopComparison` の出力契約は確定済みだが、型の公開を実値と扱わない。
- 停止状態：blocked（外部入力待ち）。R 窓前の作業は K-S• の区切りまでとの
  ユーザー指示に従い、本停止記録の保存後は作業を再開しない。
- 再開入口：ユーザーによる実 B の中継・再開指示を受け、R 後の配置と import を確認。
  `OmegaSpectrum.AdjointLoopRelativeBF.NativeLoopComparison` 型の実値 `hB` を、
  `D3TailLoopEquivalence.lean` の `nativeLoop_isQCatEquivalence_of_tailComparison hB` と
  `D3TailStability.lean` の `sp_isStable hB` へ代入する所有新葉を作る。
  ChosenLoopSourceComparison での供給なら既存 nativeLoopComparisonOfChosenSource を使う。
  条件付き版を保持し、無条件版の新葉を独自 `D3TailAll.lean` に接続する。
- 集約・監査の再実行手順（現配置。R で移動された場合は移動先へ読み替え）：
```
lake build SerrePositivity.KST.Spectra.D3TailAll
lake env lean scripts/audit_kst_spectra_d3tail.lean
```
- 監査にも無条件版の公開型検査を加え、追加仮定・公理なしを確認する。
  所有ファイルのみ保存し、K-B3 d3 向けの公開名・検証結果をユーザーへ報告する。

## 引き継ぎ
- 所有：新規 D3TailLoopEquivalence・D3TailStability・D3TailAll、
  scripts/audit_kst_spectra_d3tail.lean、本計画のみ。
- Sp-2 の D3All・D3* 葉・L9b、既存 Spectra は読み取り専用。
- B は未供給。存在・無条件 hΩ・無条件 sp_isStable は主張しない。
- 供給依頼・設計提案・結果は計画とは別にユーザーへチャットで渡す。
- 現在地：B を明示引数に持つ先行版を構成。受取型は Sp-2 と確認済み。
- 次の一手：Sp-2 の B の実公開名到着後、型検査して無条件版へ代入。
- 残りの所要時間：B の実構成は Sp-2 所管で未定。代入後は集約・監査を再実行。
- 主要宣言：nativeLoop_isQCatEquivalence_of_tailComparison、sp_isStable。
- 未コミット：なし（所有5ファイルだけを保存。他レーンの変更は含めない）。
- Sp-2 所有 D3ComparisonOutput は `420ef85a2` で保存済み（現作業木で確認）。
- 既知の問題：B の実値が未供給。条件付き先行版の型は Sp-2 と一致。

## 工程
- [x] 既存 L9b・commonChosenStageEndpointLoopIso と共通 BF 基底を照合。
- [x] ユーザー経由で Sp-2 に B の受取型を確認（回答受領）。
- [x] d3c 先行版：B を明示引数とする nativeLoop の IsQCatEquivalence。
- [x] d3d 先行版：実零対象・sp_hasFiniteLimits・指定切断・hΩ を D へ代入。
- [x] 独自集約・専用公理監査・型の仮定検査・所有ファイルのみ保存。
- [ ] B 到着後、実公開名を代入した無条件版を所有新葉に公開し K-B3 d3 に報告。

## B の供給依頼（チャットにも送付済み）
名前空間：SerrePositivity.KST.Spectra.OmegaSpectrum、
共通 BF 宣言は AdjointLoopRelativeBF。
受取型は Sp-2 所有 D3ComparisonOutput の NativeLoopComparison.{u}：
```
FunctorIso (coherentNerveMap commonRefinedEnriched)
  (commonNativeLoopEndpoint ≫ nativeLoop)
```
- commonNativeLoopEndpoint は commonOriginalInfinityMap ≫ nativeTail。
- Sp-2 は指定 loop 全図式・厳密 tail 終点を保つ実 B を供給する。
- commonChosenStageEndpointLoopIso は段別右射影の比較であり、
  それ自体を BF 全体の B として受けない。
- 実図式始点への `FunctorIso (coherentNerveMap commonRefinedEnriched)
  commonChosenLoopSource` で供給される場合、
  Sp-2 の nativeLoopComparisonOfChosenSource が既存同型と合成する。
- ユーザー経由の Sp-2 回答：受取型一致、指定図式・厳密終点の証拠は
  既存の選択族とその証明に保持。B の実値は Sp-2 が構成中。
- 型とアダプタは Sp-2 正本を import し、Sp-2b 側で複製しない。
- 再開時確認：Sp-2 の最新 L9b は B 本体を継続中と記録。
  NativeLoopComparison／ChosenLoopSourceComparison の実値は現ソースに未公開。
  工程3は外部入力待ちであり、存在を補う宣言や代替仮定を追加しない。

## 公開界面と証明経路
- nativeLoop_isQCatEquivalence_of_tailComparison B：
  commonOriginalInfinityEquivalence と commonInclusionFunctorIso ≪≫ B から
  commonNativeLoopEndpoint ≫ nativeLoop の同値を得る。
  同じ射影と既存 nativeTailEquivalence の合成を左消去し、元の nativeLoop を回収。
- sp_isStable B：実 sp_hasZeroVertex・sp_hasFiniteLimits を使い、
  nativeLoopTargetEquivalence.inv と厳密終点等号、上記 hΩ を
  Stable/LoopEquivalenceStability.isStable_of_loopEquivalence へ代入する。
- 新仮定は B のみ。有限余極限・ModelCategory・安定性を仮定しない。
- sp_isStable は B を必要とする定理。グローバル instance にしない。
- 円交換因子の直接比較・evaluationPost・uncurry・d7 は再開しない。

## 検証
- 独自集約ビルド：8919 jobs 合格。所有新葉に警告なし（既存依存の警告は再表示）。
- 専用監査：515 modules／5435 declarations 合格。標準三公理のみ。
- 私有宣言・推移的公理依存・型の ModelCategory を検査済み。
- Fibration・LocalizingInvariants、Sp-2 の D3All、未接続四葉を拒否。
- 既存 BF 構成の NonConnective.Sequential* 補助 API は既存閉包として読む。
- 公開型の検査は B 以外の仮定を要求しないことを含む。
- 共通規約どおり所有ファイルだけ git commit --only で保存する。
