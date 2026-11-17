# Codex 作業指示書 IF-W2c：段 E（KST の一般部分の取り込み）と、中核の閉包から KST・モデル圏の HA を消す

作成：2026-11-03 深夜（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex（新チャット）。
**開始**：草案（§3.0、ビルドなし）は今すぐ。適用と内部検証（§3.1、小さなビルド）は草案の承認後。**下流の一回ビルドと verify（§3.2）は暦の合図**（論文の層 2a・2b の全ビルドの後。見込み 11-06）。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) §5 段 E（R51・R52・R68・R69・R70・R56b・R45）、§4 の辺の表（R27・R64・R71・R72 の残り）、§6 の W2c 行。決定 10-28「局所化・分数・Verdier 商の API の正本を KST/LocalizingInvariants から ∞ 層へ移す」。
**共通の前提**：[IF-W0-1 §0](infinity-codex-w0-1.md)、[IF-W2b](infinity-codex-w2b.md) の §12（enforce の 3 条件）・§14（配置は宣言単位の依存で）・§16（進捗は未検証の根で）・§18（F1B は straightening 非依存）、[IF-W2a-2 §7〜§9](infinity-codex-w2a-2.md)、[DG-W3 §9・§11](dg-codex-w3.md)。判断表（補充の import・完全修飾・宇宙の明示・名前付き引数・束縛子の型の明示・局所 instance・heartbeat、いずれも v3b で一致を証明）と停止条件は W2b の最終形をそのまま使う。
worktree は `../SerrePositivity-ifw0-3`、main（3e27dda00 以降）から `infra/if-w2c` を切る。

## 1. 目的と現状（11-03 深夜の `layer_check.py --report`）

| 指標 | いま | W2c の終わり |
| --- | ---: | ---: |
| 中核層間の順序の直接違反 | 0 | 0 |
| 直接の禁止辺（すべて HomotopyLimits 発） | 18（→ KST.Spectra 16、→ HA.HomotopyFunctionComplex.AdjunctionHom 2） | **0** |
| W2a の禁止モジュール（中核の閉包にある KST・モデル圏の HA） | 150（HA 90・KST 60） | **0**（残るなら理由つきで一覧） |
| affected core | 2,531 | 0 |

W2c は二つの群からなる。**群 A**（辺を切る：R27・R64・R72 の残り）で上の指標を 0 にし、**群 B**（段 E：R51 → R68 → R52 → R69 → R70 → R56b）で KST の一般部分を Stable・Core・F1・F1B の正本へ移す。R45（LocalizingInvariants・NonConnective の残りの辺の再計測）は束の最後。

### 群 A：18 辺を切る

1. **KST.Spectra 16 辺**（HL の 12 モジュール → KST.Spectra の 11 本：PointedInterval・PointedKanWhitehead・PostMappingFibration・MappingPathSpace・PullbackKanSequence・KanSequence・PointedGroupProduct・CoherentNerve・CofibrantOmegaSequence・MonoRightHomotopyEquivalence・FibrationIntervalLifting）。計画 R27・R64 の規則：
   - 参照先が**汎用の Kan 理論**（pointed interval、Kan fibration の列、Whitehead、mapping path space、mono の右ホモトピー同値 など）なら、その KST.Spectra のモジュールとその KST 内の依存閉包（= 禁止閉包の KST 60 本の大半）を **Kan 層（`InfinityCategories/Kan/`、Pointed は `Kan/Pointed/`）へ move**。Kan 層は制限つき（Simplicial・Core・Foundation・Mathlib だけ）なので、依存閉包がそれに収まるものだけ。収まらないもの（Coherent・F1 を使う）は `Coherent/`・`F1/` へ。
   - **Spectrum\* の HL モジュール 5 本**（SpectrumBinaryProductSequence・SpectrumMappingDiagram・SpectrumPullbackAdjoints・SpectrumPullbackMonomorphisms・SpectrumTowerSequence）は spectrum 固有なので、計画どおり**上へ** `KST/Spectra/Limits/` へ move（利用者が中核にあれば止めて報告）。CofibrantOmegaSequence（Ω スペクトル）は KST に残す。
   - 判定は宣言単位（§14-3）：HL 側が実際に使う宣言 D と、その KST 内の依存。BF の fiber など spectrum 固有の定数に依存するものは KST に残し、HL 側を上げる。
2. **HA 2 辺**（HL.AdjunctionFrameHomBifunctor・HL.KanTensorAdjunction → HA.HomotopyFunctionComplex.AdjunctionHom）：R72 の規則。使う宣言が純粋（Kan tensor の随伴の Hom 表示）なら **split** して HL か Kan へ下ろす。モデル圏（HomotopyFunctionComplex の frame・Reedy）に本当に依存するなら、その HL モジュールを **ModelBridge** へ上げる（利用者が中核にあれば止めて報告）。HA の閉包 90 本はこの 2 辺だけで入っているので、切れば 0 になるはず。
3. 群 A の後の見込み：禁止モジュール 150 → 0、affected core 2,531 → 0。残る場合は、残る各モジュールの入口の辺と理由を一覧にして止めずに報告（群 B の後にまとめて判断）。

### 群 B：段 E（KST の一般部分を正本へ）

| 項目 | 内容（計画の行のとおり） | 置き先 | 本数の目安（計画時） |
| --- | --- | --- | --- |
| R51 | 一般の安定 span pushout（SConstruction/StableSpanPushout） | `Stable/` | 2 |
| R68 | lax pullback と半直交分解（L1） | `Stable/Lax/`・`Stable/Semiorthogonal/` | 56 |
| R52 | Verdier 分数の機構を**移すだけ**（LocalizingInvariants の Verdier\*・Fibration の W 分数・Tamme\*、`fraction_ho_localization`） | `Stable/Verdier/Fractions/` | 131＋90＋23 |
| R69 | 安定の cofiber・完全関手の補題（L6）、quasicategory の道具（L7）。BF fiber を使う約 20 本は KST に残す | `Stable/`・`Core/`・`F1B/` | 要再計数 |
| R70 | straightening と Kan の補助（F3）、CoreFlag（L5） | `F1/`（straightening 依存は F1B に置かない、§18） | 要再計数 |
| R56b | 比較・適用の部分（GroupoidCompletion\*・SimplexAttachment\*。閉包に DG・KST.Fibration） | `Derived/` か `ModelBridge/`（中核の外） | 要再計数 |
| R45 | LocalizingInvariants・NonConnective の残りの辺を再計測し、処置案を報告（実施は次） | — | — |

- 置き先の規則は §14-3（宣言が使う定数の定義元の層の最大値以上で最も低い層）＋ §18（straightening 依存は F1B に置かない）＋ Kan・Core の制限。
- R52 は「移すだけ」。R57（Weak\*・Tamme\* の一般版への統合）と R53・M1〜M11（新しい数学）は段 G。
- KST 側の利用者（9,495 本）は import 行だけ書き換える。K のレーン（L5・L7）は停止中、L2・L6 は凍結なので衝突しない。
- R48（Verdier の基礎ブロック 7 本）は W1 で済んでいる前提。未了なら草案で報告。

## 2. 所有範囲

- `SerrePositivity/InfinityCategories/`（Core・Kan・Coherent・F1・F1B・HomotopyLimits・Stable・F2・ModelBridge・Derived）、`SerrePositivity/KST/`（移す元。残す側の import 行）、`scripts/audit/`・`scripts/audit_*.lean`（移動に追従）、`layers.json`（例外は増やさない）、`targets/w2c-*.json`。
- 外側：EInfinity・DG・論文の層・BS の **import 行だけ**。DG の道具は変更しない。
- 変更しないもの：宣言の本文・名前・名前空間（R54 は段 F）、KST の K 固有の部分（BF スペクトル、S• 構成、局所化不変量の定義本体）。

## 3. 手順

### 3.0 草案（ビルドなし、**止めて報告する点 1**）

1. 群 A：18 辺それぞれについて、HL 側が使う宣言 D、その定義元の KST 内の依存閉包、処置（Kan へ move／split／HL 側を KST/Spectra/Limits か ModelBridge へ move）→ `targets/w2c-a.json`。適用後の模擬で禁止モジュール数・affected core の見込み。
2. 群 B：R51・R68・R52・R69・R70・R56b の対象一覧（本数を今の木で数え直す）、置き先、split が要るもの、Kan・Core の制限に触れるもの → `targets/w2c-b-r51.json` …。validator・dry-run・循環 0・`--enforce W2b` の 3 条件の模擬。
3. 下流の逆閉包の本数と時間（KST の利用者が多いので大きい見込み：12,000〜15,000 本、2〜4 時間）。
4. 止めるもの：中核に利用者がある Spectrum\*／ModelBridge 行きの HL モジュール、Kan の制限に収まらない汎用部分（→ Coherent／F1 に置けるか）、R52 で「移すだけ」にならないもの。

### 3.1 適用と内部検証（承認後、小さなビルドだけ）

1. キャッシュから復元 → before snapshot v3b（群 A・B の対象と直接の利用者）。
2. **群 A を先に適用**（コミット「群 A：辺の切断」）→ 内部ビルド → `layer_check --report`：禁止 0 を確認（残れば一覧）。
3. 群 B を R51 → R68 → R52 → R69 → R70 → R56b の順に適用（項目ごとにコミット）→ 内部ビルド（§16 の基準）→ after snapshot → 保存比較 → **止めて報告する点 2**（round の表、指標の前後、処置の件数、未説明 0）。
4. 群 B の規模が草案の見込みを大きく超える（移動 400 本超）なら、停止点 2 で Claude が下流を二回に分けるか判断する。

### 3.2 下流と verify（**暦の合図を待つ**）

1. 合図の前に main を merge（2a・2b の取り込み後。KST・HA の import 行の衝突は両方を残す）→ 静的検査の再実行。
2. 下流の一回ビルド（鍵）→ 保存比較 v3b → 層検査（3 条件、ratchet 基準の取り直し、禁止 0）→ 監査の追従 → verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`）。**条件付き事前承認**（W2b §17-3 と同じ）：下流が通り、保存比較で未説明 0、処置が判断表の範囲なら、承認を待たずに verify まで進む。
3. **止めて報告する点 3**：verify の summary、指標の前後（禁止 0）、R45 の再計測と処置案、処置の一覧、コミット一覧、段 F への入力（移した一般部分の一覧と名前空間の現状）。取り込みは Claude。

## 4. 許す変更・止める条件・禁止事項

W2b §4〜§6 と §12・§14・§16・§18 の最終形をそのまま適用する。追加：KST の K 固有の部分（BF スペクトル・S•・局所化不変量の定義）を中核へ移さない。`layers.json` に例外を足さない（要るなら止める）。

## 5. 追記（2026-11-04 朝、停止点 1 の承認：群 A の仕上げ、群 A′（R72 の残り）、群 B の置き先の規則）

**受領**：草案 1c05a5a16（ビルド 0 回）。模擬：中核層間の順序違反 0、直接禁止辺 18 → 1、禁止モジュール 150 → 106、affected core 2,531 → 2,366。群 B は探索 699 本のうち move 111・保留 588（内訳：K 固有の保留 211、混在依存の要再検討 367、一般補助の保留 10）。138 move の dry-run 終了 0、15 split の静的検査、循環 0。validator は ratchet の個別指標 26 件の増加で終了 1。下流 10,305 本・100 根・約 1 時間 43 分。

**判断**：

1. **群 A の残り 1 辺**（`HomotopyLimits.SpectrumPoint → KST.Spectra.Limits.SpectrumBinaryProduct`）：提案どおり、pointed な一点に関する 3 宣言を中核に残し、`spectrumPoint` と補助証明だけを KST へ **split**。これで直接禁止辺 0。
2. **群 A′（HA の 90 本、R72 の残り）**：許可されている HotA の基盤部分（`HomotopicalAlgebra.Simplicial` など）の中に、モデル圏側（`HomotopyFunctionComplex/Reedy`・`Quillen`・`Transfer`・`Generated`・`Monoidal`）を import しているモジュールがあり、そこから 90 本が入っている（例：`F1.TwistedArrow.TwistedHomDiagonal → HA.Simplicial.DiagonalAdjunction → Reedy.SimplexResolution`）。計画 §3 の R72 の規則をそのまま適用する：入口になっている HotA の基盤モジュールごとに、(a) モデル圏側への import が末尾の「Model」の節や未使用 import のためなら **split／prune** でモデル圏部分を `ModelBridge/`（または HotA の Model 側）へ出す、(b) 中核の利用者が本当にモデル圏の宣言を使っているなら、その利用者を **ModelBridge へ上げる**（中核に利用者が残れば止めて報告）。入口の一覧（モジュール・経路・使う宣言）を草案に加える。目標は HA 90 → 0。
3. **群 B の置き先**：「Stable へ移すだけ」が成り立たない混在依存 367 本は、**§14-3 の規則で置く**：依存が Stable に収まるものは `Stable/`、F2 の宣言を使うものは `StablePresentable/`（安定 presentable の置き場）、Derived（dg）の宣言を使うものは `Derived/`。目的は「KST の一般部分を ∞ 層へ出し、KST を K 固有の部分だけにする」ことであり、Stable の正本（一般の Verdier 分数）は段 G の M 項目で作り直す（この一覧を段 G の入力として記録）。**K 固有の保留 211 本**（BF fiber・S•・局所化不変量の定義本体を使うもの）は KST に残す。一般補助の保留 10 本（R56b）は Derived か ModelBridge。R48 の未了分があれば草案に含める。
4. **ratchet の個別指標 26 件**：W2b §12 と同じ扱い（既存経路の継承、全体は減る）。報告に経路の表、束の終わりに基準の取り直し。例外は足さない。
5. 以上で草案を更新（`w2c-a.json` に split と群 A′、`w2c-b-*.json` に置き先）→ validator・dry-run・模擬（直接禁止辺 0、禁止モジュールの見込み）を再実行 → **短い再報告（停止点 1′）** → 承認後に §3.1（適用と内部検証）。下流（見込み 10,000〜12,000 本）は 2a・2b の後に合図。

## 6. 追記（2026-11-04 朝、停止点 1′ の承認：残る HA 66・ModelBridge 8 は段 G の項目に）

**受領**：草案 11eacaa39（ビルド 0）。群 A・A′：`spectrumPoint` の分離、HA の入口 10 モジュール・13 辺の分割案で直接禁止辺 0・循環 0、禁止モジュール 150 → 74（HA 66・ModelBridge 8）、affected core 2,531 → 1,730。残り：`CosliceTwistedHomEquivalence` の証明が Reedy の定理を実際に使い、ModelBridge へ上げると中核の `SourceInitial`・`RightRepresentableTwistedArrowEquivalence`・`TwistedHomFunctorMap` に実参照が残る。群 B：混在 367 本のうち 177 本を丸ごと move、92 本から一般宣言を split、98 本を保留、K 固有 211 本は KST に残す、R56b の 10 本は Derived。325 move の dry-run 終了 0、116 split の静的検査、`--enforce W2b` PASS、validator の増加は承認済み 26 指標のうち 14 件。下流 11,152 本・129 根・約 1 時間 51 分。段 G への一覧 `w2c-stage-g-input.json`。

**判断**：
1. **承認**。§3.1（適用と内部検証）へ進んでよい。下流と verify は 2a・2b の後の合図（2a は 11-04 朝に取り込み済み。2b は 11-05 見込み）。
2. **残る HA 66・ModelBridge 8**：`CosliceTwistedHomEquivalence` → Reedy の依存は数学的な依存（twisted arrow の coslice の Hom の同値を Reedy の定理で示している）で、移動では切れない。**W2c の完了条件はこの残りを除いて判定する**（直接禁止辺 0、禁止モジュール 150 → 74、残りの入口と理由を一覧に）。残りは段 G の項目 **M16**：「`CosliceTwistedHomEquivalence` の Reedy 非依存の証明（Kerodon の twisted arrow の議論で書き直す）か、F1 の twisted arrow の該当部分の再編」。計画の段 G に追加（Claude）。`layers.json` の例外は足さない（ratchet の基準で保つ）。
3. 群 B の保留 98 本と、Stable に置けなかった分数（StablePresentable・Derived に置いた分）の一覧は、段 G の M 項目（一般の Verdier 分数の正本）の入力として `w2c-stage-g-input.json` のまま残す。
4. ratchet の 14 件は W2b §12 の扱い。

## 7. 追記（2026-11-04 16:00、停止点 2 の承認と下流の合図）

**受領**（555ed8bdc）：内部ビルド 1,086/1,086 PASS（群 A 6 round、群 B 8 round。round 7 の再発 1 件は補充の宛先の誤りで解除）。保存比較の生差 58 件を個別照合し未説明 0。直接禁止辺 0、残余 74（HA 66・ModelBridge 8、M16）。匿名 instance 8 件の元名を明示（before と同じ名前に固定）、private 参照は `import all` で復旧。

**判断**：
1. 承認。`import all` による private 参照の復旧は、宣言の意味を変えない処置として受け入れる（v3b で一致済み）。ただし private の境界を越える参照なので、件数とモジュールを停止点 3 の報告に一覧で書き、段 F（R60 の台帳）で「private を公開にするか、参照側を元のファイルへ戻すか」を判断する項目にする。
2. **下流を合図する**：main（2a・2b・BS-W10 作業 A・`pairCompletionH0Unit` を含む）を merge（HA/DerivedCompletion と BS の import 行の衝突は両方を残す）→ 静的検査の再実行 → 下流（見込み 11,000 本前後、約 2 時間、鍵）→ 保存比較 v3b → 層検査（3 条件、ratchet の取り直し、直接禁止辺 0）→ 監査の追従 → verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`）。**条件付き事前承認**（§3.2-2）：下流が通り、保存比較で未説明 0、処置が判断表の範囲なら、承認を待たずに verify まで進んで停止点 3 を報告。
3. 停止点 3 の報告：verify の summary、指標の前後（直接禁止辺 0、禁止 150 → 74、affected core）、R45 の再計測と処置案、`import all` の一覧、段 G への入力（`w2c-stage-g-input.json` と M16）、コミット一覧。取り込みは Claude。

## 8. 追記（2026-11-04 22:05、verify の対象収集の穴：∞ の道具の修正依頼）

論文の層の B4 の verify（1e15322b6）で `audit_infinity_f1` が失敗した。原因は、この監査が `run_cmd` の中の `importModules` で F1/Diagrams のモジュールを読み込むが、verify はビルド対象を監査ファイルの `import` 行からしか拾わないため、それらの olean がない環境で落ちること（G1 の取り込みで入った経路。G1・W2c の worktree では olean が残っていて表に出なかった）。main では PASS。

**依頼**（∞ の道具、ビルドなし、別コミット、試験つき）：`verify_runner.py`（または監査の準備段）が、監査ファイル中の `importModules` の引数（モジュール名の配列リテラル）も監査対象のビルドに加えるようにする。それが難しければ、監査ファイル側に同じモジュールを通常の `import` 行で足す（監査の生成規則に「`importModules` で読むモジュールは `import` 行にも書く」を加える）。どちらにするかは草案で報告。段 F の指示書と一緒に出すので、それまでは草案だけでよい。
