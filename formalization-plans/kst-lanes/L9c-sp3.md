# Sp-3 — Sp-6 s3・s5 専用計画

更新：2026-10-28。正本：L9-spectra.md。Sp-2 から s3・s5 を分割。

## R 窓前の停止・R 窓後の再開入口（2026-10-28）
- 現在地コミット：Lean 消費側・専用集約・監査は `50009ed9e`、供給待ち記録は `807b41597`、設計見積りまでの計画保存は `0115a9e8b`。
- 待っている供給：K-S• ③ の `dgOdotMilnorActualRectangle` の共通 S 長方形上の三認証（右面・外周の VerdierSquareDiagramIso と、上下指定二単体を保つ VerdierRectangleDiagramIso）、または `DGOdotMilnorActualRectangleInput R d h` の実構成の公開名。
- R 窓前は新規 Lean 作業を始めない。③ の実代入は供給の到着にかかわらず R 窓後に行う。s3 無条件化・最終 s5 は未完了。
- s3 再開入口：`Spectra/S3MilnorConnection.lean` の `SerrePositivity.KST.Spectra.S3.milnorActualInput` に実図式・指定境界・三認証・kernel_vertex を一回で代入する。既存入力型で届いたら直接消費する。
- 続いて `S3.milnorActual_isPullback`・`S3.milnorSourceRoof`・`S3.milnorSourceValueIso` へ接続し、未供給の認証を引数に残さず結論を公開する。K-B3 への供給条件は下記の区別を保持する。
- s5 の検証手順：`lake build SerrePositivity.KST.Spectra.S3All` → `lake env lean scripts/audit_kst_spectra_s3.lean` → 所有パスの `git diff --check`。公開名・残仮定・引き継ぎを更新し、`git commit --only <所有パス>` で保存してチャットで報告する。
- 停止前確認：2026-10-28 に所有集約ビルド成功（13522 jobs）、専用監査成功（所有3葉24宣言・標準三公理のみ・推移的90,721定数に ModelCategory なし）。所有 Lean ソース・監査に差分なし、計画の git diff --check 成功。停止準備完了。

## 所有・共通規約
- 所有：KST/Spectra/S3*.lean の今回の新規4葉（下記）、scripts/audit_kst_spectra_s3.lean、本計画（≤300行）。
- 既存 Spectra 葉・Spectra.lean・LocalizingInvariants・L9・L9b は読み取り専用。
- Sp-2 の PointedUncurry*・PointedParametric*・D3* の未追跡 WIP は変更も新規接続もしない。
- sorry・追加 axiom・ModelCategory 仮定を禁止。KanQuillen を import しない。
- 固定 S・ν・K と元の I・P を保持する。新たな不変量条件・一般商 API は導入しない。
- git commit は必ず --only と所有ファイルの明示列挙で行う。
- 供給依頼・設計提案・完了報告は本計画だけで済ませずユーザーへチャットで渡す。他チャットには送信しない。

## L9 からの採用済み条件の転記

### Sp-6 s3 の接続口（採用済み、具体的入力の存在は未供給）
- 採用済み修正：固定 ν の Perf 商辺は strict Verdier 商でなく冪等完備化までの列。K-S• 正本 PerfectVerdierSequence（実 strict 商＋完備化）を使う。Sp の RelativePerfectVerdierDiagram.ofSquare／ofStableSquare、RelativePerfectVerdierRectangle.ofActualFaces と境界付き全源比較・全 ν 像比較で、Cat^perf 不変量の同じ制限の pullback を得る。ofStrict は元の四角形・長方形と恒等完備化を保ち、完備性を追加入力にしない。D-21 は K-S• の dgOdotMilnorCompletion／_isIdempotentCompletion に特殊化済み。実二面からの comparison_isPullback_of_actualFaces と、絶対 Cat^perf 長方形への comparison_isPullback_of_actualFaces_imageIso、同じ全比較成分を使う rectangleValueIso_of_imageIso／_triangle を提供。実長方形・全比較の一体化は未供給。新たな不変量条件や一般商 API は導入しない。
- 固定 S・ν・K を保ち、零角に A/A を使う。対象別 ε からの自然な収縮を構成せず、全対象商からの厳密延長を用いる。
- 具体的 S 長方形 F の実際の ν 像を、右面・外周の Verdier 証拠で認証する。独立に選択した絶対 Tamme 長方形との厳密等号 image_eq に代えて、指定境界を保つ全図式 FunctorIso を接続口に追加する。既存の厳密等号版は特殊化として保持する。
- 元の包含・商・四辺と二つの合成三角形を明示して保持する。始域回収は元入力への増大屋根と ν 像の指定同値で受け、S 内の source_vertex_eq を主経路で要求しない（17:53 採用、RelativePerfectVerdierSourceRoof で受ける）。旧等号版は特殊化として保持する。絶対 PerfectVerdierDiagram の認証から同じ実 ν 二面へ全比較を運び、同じ実 S 長方形の値で貼合せを消去する。辺の関手同型だけから全図式比較や S 内の厳密代表を推論しない。長方形と全図式比較の存在は未証明。
- K-B の DGKappaSuspensionRelativeRoofInput は現行の型で受けられる。I・P は変更せず、実核・指定収縮・Verdier 証拠・零角の Perf 値の零性の供給後に exists_dgFixedNullRelativeRoof を適用する。一般分数比較の充満忠実性は s4 で供給済み。


## 工程・現在の到達点
- [x] (1) 三認証をそれぞれ明示引数にする消費側骨格を実装。認証の存在は主張しない。
- [x] ofSquare／ofStableSquare → ofActualFaces の厳密像版の特殊化を接続。
- [x] 同じ実二面の相殺、全比較に沿う LT 面の pullback、同じ比較成分による始域回収と可換式を接続。
- [x] K-B3 の既存 toStrict を直接保持し、strict 屋根の同じ Perf 図式を認証。
- [x] exists_dgFixedNullRelativeRoof の既存経路へ接続。零角 A/A の零性は実証済み定理を代入し、追加引数から除く。
- [ ] (2) K-S• ③ の公開実構成を代入して s3 を無条件化する。
- [x] (3a) 消費側骨格の専用集約をビルド。
- [x] (3b) 専用監査・公開型の仮定検査を完了。
- [ ] (3c) 実認証の代入後に集約・監査を再検証し s5 を完了。

## 公開 API（namespace SerrePositivity.KST.Spectra.S3）
- S3ActualFaces.lean：actualFaces_isPullback は実 S 比較面と絶対 LT 比較面の pullback を同時に返す。右面 er・外周 eo・全長方形 e は独立した明示引数。
- actualSourceValueIso／actualSourceValueIso_triangle は元入力への増大屋根を受け、全比較の同じ成分と屋根の可換式を保つ。
- rectangleOfSquare／rectangleOfStableSquare は既存 image_eq の厳密版の特殊化。Perf 商辺には PerfectVerdierSequence の completion を保持する。
- S3MilnorConnection.lean：milnorActualInput は同じ R・d・h の三認証と kernel_vertex を DGOdotMilnorActualRectangleInput に一回で束ねる。
- milnorActual_isPullback／milnorSourceRoof／milnorSourceValueIso／milnorComparison_triangles は同じ入力を消費し、始域等号を元対角入力には要求しない。
- S3KappaConnection.lean：kappaToStrict は DGKappaRelativeRoofComparisonInput.toStrict を直接渡す。
- kappaPerfectDiagram／kappaPerfectDiagram_square／kappaPerfect_isPullback は同じ strict 屋根を恒等完備化の特殊化として評価する。
- exists_kappaRelativeRoof は実核 A・元の i・指定 ContractedFunctor C・合成照合 hC・strict Verdier 証拠 hV を明示して既存屋根を返す。零角の零性は dgFixedNullInput_isZeroCategory を代入済み。
- S3All.lean：上記3葉だけを新規登録する独自集約。共有 Spectra.lean の登録は統合担当へ委ねる。

## 供給依頼（チャットでも通知済み）
- K-S• ③：DGOdotMilnorActualRectangleInput R d h の実構成の公開名、または同じ実 S 長方形 G と右面・外周・全長方形の三認証、指定境界、kernel_vertex を供給してほしい。
- 三認証は指定包含辺・完備化後商辺・零角と、上下二単体の制限等式を保持すること。
- 始域屋根自体は dgOdotMilnorRelativeSourceRoof で供給済み。元対角入力との S 頂点等号は不要。
- K-B3 e：strict 屋根の実供給には実核・指定収縮・元の商射の strict Verdier 証拠が必要。Perf 完備化付き二面認証からその証拠を推論しない。

## 設計上の区別（チャットでも通知済み）
- ν 像の全 FunctorIso から RelativePerfectVerdierDiagram の image_eq を作るのではなく、comparison_isPullback_of_actualFaces の実二面経路を使う。
- image_eq 付き版は rectangleOfSquare／rectangleOfStableSquare に保持する。全図式同型から辺の厳密等号を勝手に得ない。
- Milnor 入力と Kappa 屋根の入力の同一性は未証明。二つの接続口の存在だけで K-B3 への実供給完了とは数えない。
- kappaPerfect_isPullback の値は dgKInputPerfectNu ≫ E。これを元の固定 dgKInputK と同一視するには K-B3 の既存の値照合を使う必要があり、新しい K は選ばない。

## 検証・引き継ぎ
- lake build SerrePositivity.KST.Spectra.S3All：成功（13522 jobs）。
- lake env lean scripts/audit_kst_spectra_s3.lean：成功。所有3葉24宣言は標準三公理のみ、推移的90,721定数に ModelCategory なし。主要11公開型を確認。
- git diff --cached --check（所有6ファイル）：成功。
- 消費側骨格の実装・検証完了、公開名と残る供給依頼はユーザーへチャットでも報告済み。
- 専用監査は所有3葉の私有宣言も列挙し、公理依存と推移的な型・証明依存の ModelCategory を拒否する。期待モジュールと主要公開型も検査する。
- s3 全体と s5 の実供給完了は未認定。依存：K-S• d④③ → s3 → K-B3 e。
- 再開時：K-S• ③ の公開実構成名を確認し、milnorActualInput または既存入力型へ一度代入。三認証を未解決引数に残さず実結論を公開して専用集約と監査を再実行する。

## 供給待ちの再確認（2026-10-27）
- 初回実装と続く2回の継続で、同じ K-S• ③ の未供給を確認。上流最新保存は `61a34e775`。
- L1 正本の冒頭は共通 S 長方形・上下指定二単体・三認証を未完と明記。ソースにも `DGOdotMilnorActualRectangleInput` の実構成は未供給。
- 個別右面・外周の既存認証だけでは、共通長方形への制限と全長方形比較を代替できない。
- 工程(1)と骨格の集約・監査は完了。工程(2)・最終 s5 は外部供給を必要とし、所有範囲で先行できる残工程なし。
- 目標は未達。供給待ち（blocked）とし、実構成の公開名が届いたら同じ代入口から再開する。チャットにも供給依頼を報告。

## 非連結 K 設計案への Sp-3 見積り（2026-10-27、実装着手なし）
- s3 の優先順位・blocked は維持。本節は ∞ Verdier 商 API 拡張の見積りのみ。
- 現状修正：IsVerdierSequence.universal は同宇宙の任意 quasicategory E に対する localizationPrecomposition の IsQCatEquivalence を既に返す。関手圏上の普遍性は存在レベルだけではない。
- exists_verdierQuotientCone* は与えられた商の有限錐回収であり、一般商の存在定理ではない。IsVerdierSequence は商の存在を主張しない。
- 流用：IsLocalization.precomposition_isFullyFaithful／exists_extension、inverts_iff_kills_inclusion、FunctorIso と内部 Hom、既存の宇宙移送。
- 暫定工数（1人、実装・局所検証込み、供給待ち除外）：核を保つ一つの射の延長と指定全比較 1〜3人日、完全関手圏への普遍性の制限と自然変換 3〜5人日、全高次整合を持つ商族の ∞ 関手と独立監査 5〜10人日。合計9〜18人日を計画枠とする。
- 前提：対象ごとの商・安定性が供給済みで、入力族の正しい写像空間モデルを使えること。Indκ・compact 保存・一般商の存在・冪等完備化の関手性・Cat∞ 値 straightening 全体・K の局所化定理はこの枠に含めない。
- 最大リスク：点ごとの Classical.choose を並べても全高次整合は出ない。既存 straightening の基底・値の適用範囲は個別確認を要する。
- 接続：s3 の固定 ν・PerfectVerdierSequence・指定全図式比較・始域屋根は継続利用でき、strict dg 懸垂自己作用は追加しない。
- チャットでも上記の現状修正・粗見積り・除外範囲を報告する。
