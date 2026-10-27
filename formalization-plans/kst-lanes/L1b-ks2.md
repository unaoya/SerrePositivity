# K-S2：K-10 d②・e②・厚核側の下指定二単体

## 引き継ぎ（2026-10-27）
- 現在地：入力型をユーザー経由で K-S• に確認済み（変更予定なし）。
  実構成の予定公開名は `dgOdotMilnorActualRectangle`（未定義・未着）。
  d②・e②骨格・厚核下三角形比較の独自集約ビルド成功（13,687 jobs）。専用監査も73宣言・3葉で成功。
- 残り：厚核下指定二単体と共通長方形の照合 →
  三認証の実構成代入による e② の無条件化 → 公開名中継・閉鎖。
  原典：D2 G-1 f、Tamme §1、Land–Tamme §1.2 Lemma 1.11・§2。
  見積り：下段境界確定後の接続1〜3時間、三認証代入・監査0.5〜1時間（納期ではない）。
- 主要宣言（独自集約検証済み）：`dgOdotTailPerfectGluingLaxEquivalence`・`dgOdotTailNativePerfLaxEquivalence`・
  `dgOdotTailNativePerfLax_fst`・`dgOdotTailNativePerfLax_snd`・
  `dgOdotTailNativePerfLax_cone`・`dgOdotTailResolvedProjectionComparison`・
  `dgOdotTailKernelLowerTriangleComparison`・
  `dgOdotTailKernelAbsoluteLowerTriangleComparison`・`dgOdotTailCatPerfConnection`。
- 依存と提供：D2 と K-S• の公開葉を読み取り専用で接続。
  所有は `DGOdotTail*.lean`、`OdotTailAll.lean`、専用監査、本計画。
  K-S• の既存葉・`SConstruction.lean`・L1・Cofinality は変更しない。
- 未コミット：なし（本保存単位の所有6ファイルのみを保存）。
- 既知の問題：三認証の供給待ち。個別恒等面・厚核外面の認証は共通長方形の完成と数えない。
- 次の一手：共通長方形の下段三頂点・二辺・合成辺を固定し、
  外面の下三角形比較から下段合成二単体への接続を構成する。

## L1 の K-10 三段目（着手時の転記、正本は L1）
- **K-10 d②〜d④・e② 三段目（固定）**：
  1. [ ] d②：D2 の Milnor 条件・実 lax 比較・cell 平坦商の型を照合する。
  2. [x] d③：元対角の充満忠実性と thick 核・局所化を Milnor 条件から接続する。
  3. [x] d②〜③：固定 S・ν の主経路を resolved 射影へ接続する。
  4. [ ] d④：Sp の零角・実面・長方形比較を接続し、未供給の全図式入力を分離する。
  5. [ ] e②：四完備性を保持して Cat^perf の実商入力と LT 結論へ接続する。
  6. [x] 集約・公式監査・禁止仮定検査を通し、引き継ぎを保存する。
- **残りの順序**：d④② の元二脚・恒等二脚・元 corner cone は三つとも無条件供給を代入。
  ③ の元実逆回転後の合成全比較、上下指定二単体、共通 S 長方形と三認証を続け、
  その後 d②、e② へ進む。個別恒等実面の認証は共通長方形上の三認証の完成とは数えない。
  三認証の消費側は Sp-3（10-27 の中継指示）。公開名が出たらユーザー経由で即時中継。
  S4 は第 II 段。

## K-S2 の分担と設計
1. d②：D2 の元二脚・恒等二脚・corner cone の公開入力型を保持。
   native gluing → 係数 lax → 元 Perf lax の実合成同値で両射影と実差を回収し、
   同じ native resolved 射影を比較の単位で回収する。Milnor 条件は明示引数。
2. e②：`DGOdotCatPerfInput` の四完備性を `dgOdotCatPerfInput` から受ける。
   coherent 完備性は既存 `DGKInputIdempotentComplete` と D 正本を使い、H⁰ から自作しない。
   同じ resolved 商・実完備化を保持し、三認証を含む `ActualRectangleInput` を一回入力。
   元実面・全長方形の引き戻し、実列の fiber 性、元始域の屋根同型を接続する。
   resolved 完備化先と元 ⊙ の同定を追加の仮定で代用しない。
3. 下二単体：`7404a60a5` の LT 外周→厚核面の全比較を下三角形へ制限し、
   公開核面全比較の下制限と合成し、`dgOdotMilnorNuNullSquareComparison_lower` と
   `dgOdotMilnorNuNullPerfectSquareComparison_precomp_postcomp_heq` で元指定値を回収する。
   元指定包含・商短辺の回収を保つ。これは外面の下三角形の比較であり、
   共通長方形の `pastingBottomTriangle` の構成とは別に照合する。
4. 未公開の `DGModuleConeConnectingFamilyNaturality`・`DGCellIdentityGraphYonedaNative` 等は
   直接 import しない。三認証が届いたら同じ接続口へ一回代入する。

## 供給依頼（チャットでも送付済み）
- 既存 `DGOdotMilnorActualRectangleInput R d h` と同じ型を採用することを確認済み。
- `diagram` と right/outer の BoundaryIso・DiagramIso、全長方形の BoundaryIso・DiagramIso、
  `kernel_vertex` を持つ実構成を③で供給予定（`dgOdotMilnorActualRectangle`）。
- 厚核下指定二単体を共通長方形へ接続する公開比較名は確認済み。
  `NuNullSquareComparison_lower` と Cat^perf 回収を使い、指定値を保持する下比較を構成済み。
  `dgOdotTailActualKernelLowerTriangleComparison` と
  `dgOdotTailActualKernelAbsoluteLowerTriangleComparison` は外面認証だけを受ける。
  共通長方形の下段三頂点・二辺・合成辺の公開名を追加照会したが、
  回答は既存型・公開比較の再確認のみで、下段の具体的指定は未確定。
- K-S• の③本体や作業中ファイルは編集・直接 import しない。

## 検証・保存
- `lake build SerrePositivity.KST.SConstruction.OdotTailAll`
- `lake env lean scripts/audit_kst_s_construction_tail.lean`
- 結果：集約13,687 jobs成功、公理監査73宣言・3葉成功。
- import 閉包9,880モジュール、未追跡上流葉なし、指定作業中2葉の依存なし。
- 新規 sorry・公理・ModelCategory 仮定・検証上限増加なし。
- 公理は propext・Classical.choice・Quot.sound のみ。
- import 閉包を確認し、未公開作業葉が入る場合は公開入口の分割をユーザー経由で依頼。
- `git commit --only <所有パス>`。供給依頼・設計提案・完了報告は必ずチャットでも渡す。
- 全工程完了後に R 第2窓の前に閉鎖する。
