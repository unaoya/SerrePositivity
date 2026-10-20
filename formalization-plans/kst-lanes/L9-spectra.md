# K-L9（Sp・ホモトピー群）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-Sp。L9e の後、γ3 を使って Sp の ∞ 極限と安定 ∞ 圏としての Sp（局所化不変量の値域）。

## 引き継ぎ（2026-10-21）

### 現在地
- **K-5 抽象部分へ移行（ユーザー指示）**：安定 ∞ 圏・完全関手、抽象 Verdier 列、Sp 値の局所化不変量と基本補題を担当する。K-S• の SConstruction と D の Stable/・Drinfeld 商は読み取り専用。以下の K-5 節に界面と残工程を固定する。
- K-5：StableInfinity・抽象 Verdier 列・零安定圏・任意抽象列の coherent 四角形提示、その像の実 fiber 性と BF fiber の全整数 π による同値検出は完成。元の homotopyFiber を左下頂点、元の射を右辺に持つ Sp の実 fiber 四角形の下辺を、元の homotopyFiberInclusion の射の類まで照合した。整数 π は h Sp 上の実関手となり、元の BF 整数 π 関手との自然な比較も完成。h Sp での切断だけから fiber 群の積分解まで拡張した。任意 fiber 四角形への長完全列の移送と Sp の積同値は未完。
- K-5 の今回の検証：専用対象5571 jobs、32モジュール・435宣言の専用公理監査、全体19116 jobs が終了コード0。標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
- **優先順を変更（ユーザー指示）**：d1 整数次数による同値検出 → d2 値域界面の固定。IsStable は I-b 末尾へ延期。evaluationPost circle と逆関手経路は再開しない。停止中の4 WIP は保持する。
- L9a・L9b・改訂 L9c・L9d・L9e 完了。骨格の成分・高次係数表示、微分の符号と核・像、Milnor の全整数次数界面と lim¹、Mittag–Leffler 収束、有理有限群の標準 Shapiro 同型、通常 Tot・BF・元の homotopy Tot の比較まで完了。
- Sp の零対象、小積、任意の coherent cospan、通常の小圏上の BF 図式の ∞ 極限、元の hG/Tot の実際の ∞ 極限錐、任意射の fiber と整数 π の長完全列は完成。
- nativeTailEquivalence は完成。nativeLoop は全単体上の関手で、実 loop 四角形・円 cotensor との関手同型・対象ごとの tail との両合成の同型・本質的全射性は完成。nativeLoop の完全忠実性と ∞ 圏同値性は未証明。
- d1 の証明を完成：標準整数 π の同型性を任意段の標準基点へ移し、path fiber の任意基点での五項比較から点つき Kan 複体間の loop 射の全基点同型性を得て、構造随伴の厳密な自然性で各段の全基点へ戻した。PiIsomorphism と全段 KanPiIsomorphism の同値、元の BF 射と任意の Sp の一単体の可逆性を証明。対象・集約ビルドと専用監査まで成功。
- d2：下表を K-S• の K-5〜K-8 が使う Sp 値域界面の正本とする。提供済み行だけを無条件に使用し、未提供行を入力公理・追加 instance で埋めない。Sp の安定性・一般の完全関手 API は I-b 末尾まで要求しない。
- 今回の検証：対象・集約 6617 jobs、監査 1446 モジュール・13123 宣言、標準三公理のみ。ともに終了コード 0、宣言型の ModelCategory 検査も成功。全体 19003 jobs も終了コード 0。全体 diff --check も成功。

### 残り（依存順）
- d1 完了：PiIsomorphism と全段・全基点 KanPiIsomorphism の同値と、任意の Sp の一単体の同値検出を検証済み。BF §2、Goerss–Jardine I §§7–8。
- d2 の宣言表固定は完了。未提供行の実装は今回の宣言表固定とは別の後続項目。任意 coherent 極限・全有限極限の一般界面は F1b/F2 の既存 HasColimit から Sp へ接続する（HTT 4.2.4.1、規模未再見積もり）。一般 γ4 の完成待ちや再実装へ戻らない。
- d3：IsStable は I-b 末尾。d1・d2 の固定と他の優先項目の消化後だけ、旧経路の六段階を再開する。HA §1.4.2、従前 24–48 時間以上（上限保証なし）。現時点では着手しない。

### 主要宣言：Sp 値域界面（共通接頭辞 SerrePositivity.KST.Spectra）

| 項目 | 宣言 | 型・範囲・状態 |
| --- | --- | --- |
| 値域 | Sp、sp_quasicategory | BF Ω スペクトルの coherent nerve。宇宙 u の BF 対象から SSet.{u+1}。提供済み |
| 零対象 | OmegaSpectrum.pointZeroVertex、OmegaSpectrum.sp_hasZeroVertex、OmegaSpectrum.functorZeroVertex | Sp と任意 Fun(K,Sp) の実零対象。提供済み |
| 小積（有限積を含む） | OmegaSpectrum.SmallProduct.obj、projection、infinityCone、infinityCone_isLimit | S : Type u の族、Discrete S の元の錐の IsLimitCone。提供済み |
| cospan・pullback | OmegaSpectrum.CoherentPullback.infinityCone、infinityCone_isLimit、hasLimit | p : horn 2 2 → Sp に HasLimit p。任意の coherent cospan。提供済み |
| 通常の一般小図式 | OmegaSpectrum.homotopyLimitCoherentCone、homotopyLimitCoherentCone_isLimit、strictCoherentDiagram_hasLimit | I : Type u、SmallCategory I、D : I ⥤ OmegaSpectrum に HasLimit (strictCoherentDiagram D)。提供済み。任意の coherent 図式と混同しない |
| fiber 列 | OmegaSpectrum.sp_fiber_exists、fiberSquare、homotopyFiber、homotopyFiberInclusion | 任意の Sp の辺の実 fiber 四角形、および実 BF 射の指定 fiber。提供済み |
| 整数 π と長完全列 | OmegaSpectrum.homotopyGroup、homotopyMap、homotopyGroupEquivAt、homotopyFiberBoundary、homotopyFiberLongExact | j : ℤ の可換群と実 BF 射への作用、全整数次数の三箇所の完全性。提供済み |
| 有限極限全体 | 予定 OmegaSpectrum.sp_hasFiniteLimits | HasFiniteLimits Sp（全有限 K : SSet.{u+1} と任意 p : K → Sp）。有限形状の小宇宙への縮小・錐の移送を含む一般の包装は未提供。提供済みの積・cospan を使用し、一般 coherent 図式の極限の接続後に供給する |
| 同値検出（d1） | OmegaSpectrum.PiIsomorphism.levelwise、piIsomorphism_iff_levelwise、isInvertible_of_piIsomorphism、spEdge_isInvertible_of_piIsomorphism | 標準整数 π 同型 ⇒ 各段の全基点 π 同型 ⇒ 元の Sp の辺の可逆性。対象・集約・専用監査成功、提供済み |
| tail の同値 | OmegaSpectrum.nativeTail、nativeTailEquivalence | 元の全単体上の関手を順方向に持つ QCatEquivalence Sp Sp。提供済み |
| Ω と tail の比較 | OmegaSpectrum.nativeLoop、nativeLoopCircleFunctorIso、nativeLoopTailVertexIso、nativeTailLoopVertexIso、nativeLoop_essentiallySurjective、予定 nativeLoopEquivalence・nativeLoopTailFunctorIso・nativeTailLoopFunctorIso | Ω の実関手と対象ごとの比較は提供済み。QCatEquivalence Sp Sp（hom = nativeLoop）と両合成から恒等関手への FunctorIso は未提供・I-b 末尾。K-5〜K-8 はその完成を先取りしない |
| 任意の coherent 図式の極限 | F2.hasColimit_coherentSpaceDiagram、F2.coherentDiagramTotalCocone_isColimit（InfinityCategories.F2 集約）、予定 OmegaSpectrum.coherentDiagram_hasLimit | F1b の空間値 HasColimit（B : SSet.{u}、ulift B → SpaceInfinity.{u}）を読み取り専用で使用。Sp の任意 D : ulift B → Sp の HasLimit への移送は未提供。空間の HasColimit だけを Sp の HasLimit と主張しない |
| 安定性 | 予定 sp_isStable | IsStable Sp は未提供。I-b 末尾の d3。K-5〜K-8 の現段階の前提にしない |

### 依存と提供
- Mathlib・既存 Spectra/・HomotopicalAlgebra/Simplicial/・InfinityCategories/ は読み取り専用。型の正本は Lean、運用は foundations.md §8。
- γ1 は coherent nerve の quasicategory 性、F0 は同値と極限の普遍性を供給。任意 coherent 図式の極限の次の入口は F1b/F2 の上記 HasColimit とする。
- K-S• の K-5（局所化不変量の定義）・K-6（Verdier 列の fiber 性）・K-7（BGT 非連結化）・K-8（Tamme・Land–Tamme）は上表の界面だけを使う。BF の符号・厳密化・evaluationPost の内部へ依存しない。K-7 に必要な一般 coherent 極限は未提供行の移送の完成後に消費する。
- 外部提供は零・実極限錐・実 fiber と整数長完全列・同値検出、および既存の有理化・Tot・hG・骨格障害計算。局所化不変量の定義・K の合流そのものは K-基盤所有。

### 未コミット
- 停止中の未追跡 WIP：PointedUncurryActionTensor.lean、PointedParametricUncurryAction.lean、PointedUncurryComposition.lean、PointedParametricUncurryPre.lean。集約・監査に接続しない。前二つは単体ビルド成功、Composition は失敗、Pre は未検証のまま保持。
- d1・d2 と K-5 の32モジュールは保存単位として検証済み。今回の12新規モジュール・BFFiberInfinityCone の精密化・専用集約・監査・二つの指定計画だけを保存する。D 計画への判定要求追記は既存の他レーンの未保存差分と同居するため今回のコミットに含めない。停止中4 WIP と共有ルート・他レーンの差分は保持する。

### 既知の問題
- Sp の IsStable、Ω の完全忠実性・関手同値、任意の coherent 図式への極限の移送は未完。いずれも上表で未提供と明記し、存在を仮定する構造体で完成扱いにしない。
- **逆関手案の再評価（2026-10-21、依頼の1時間以内）**：残る正確な十分補題は、全 BF 対象 X,Y について、A := sourceMap CirclePower.space X Y、e := tracedOriginalLoopModelMap X と置いたときの実ホモトピー `H : SSet.Homotopy (A ≫ signedEvaluationAt X Y e).right (kanAdjointTracedUnitFamily X Y A).right` の構成であり、既存の evaluationPost_circle_piIsomorphism_of_raw_traced_homotopy に渡せば元の evaluationPost circle の全基点 π 同型性を得る。H を作る旧経路は下記の6段階、従前見積もり24–48時間以上（上限保証なし）。代替は①有限極限の全形状・宇宙を含む包装、②Ω と tail の関手同型、③逆関手による QCatEquivalence の組立、④一般安定性判定の4工程。①・②・④は未完で、総時間は少なくとも複数日の暫定評価、上限は未見積もり。特に②の前提「構造随伴が厳密な単体的自然変換になる」は Ω 条件から未導出：ordinaryStructureAdjoint_comm_iff は二重随伴 b の `b ≫ swap = b` を要求し、その厳密等式は swap の π₀ 作用が恒等であることまで強制する。さらに BF cotensor は単射置換を含み、cotensorPost は選択した持ち上げで厳密な関手法則を持つ API ではない。nativeLoop と nativeCotensor は全単体上の関手だが、元の BF 圏上の厳密な豊穣 Ω 関手が提供済みとは扱わない。構造随伴の向きも id ⇒ Ω∘tail であり、tail∘Ω ⇒ id には可逆化と両合成の照合が別途必要。StrictEnrichedTransformation.functorIso は既に実装され成分の可逆性から実 ∞ 関手同型へ移送できるため、N への追加要求はない。HA Cor. 1.4.2.27 の判定自体は正しいが F3 に該当宣言はなく、D 計画へ要求を記載。自前実装の配置先は Spectra 配下とし Stable は変更しない。②の厳密化を解消せず短縮とは判定できないため、今回の評価では切り替えず、evaluationPost の計算も再開しない。
- d3 の保留位置：①全族正方形の uncurry・評価への移送、②元の自然性・逆三角形との境界照合、③主構造正方形（左 kanAdjointTracedStructureInterval、右 tracedSourceUnitStructureInterval）、④SpecifiedCodifference、⑤標的単位との貼合せ、⑥自由 cotensor・相対 StrictInterval による raw 全 Hom H を evaluationPost_circle_piIsomorphism_of_raw_traced_homotopy に渡す。旧実入力 kanAdjointSignedReverseParametricSquare と全境界は保存済み。
- 所有ソースの sorry・追加 axiom・ModelCategory 仮定を禁ずる。公理監査は私有宣言・推移的依存・宣言型の ModelCategory 定数を検査する。KanQuillen は import しない。

### 次の一手
- K-5：次は任意の fiber 四角形を元の BF homotopyFiberSquare と比較する。安定性不要の nonempty_cofiberSquareFunctorIso を dualSquare で双対化する入口を確認済み。四角形全体の関手同型と各辺の自然性を保持し、piFunctor・piComparison_naturality で元の BF 長完全列を任意の像の fiber 四角形へ移す。最後に coherent な切断付き列の Sp 積同値を構成する。群の積同型だけで完成扱いにしない。
- 今回の d1・d2 は工程完了。整数次数による同値検出の証明・宣言表固定と対象・集約・監査・全体ビルドは成功。宣言表の未提供行まで完成したとは扱わない。
- 一般 coherent 極限の実装を再開する際の最初の工程は、F2.hasColimit_coherentSpaceDiagram から任意 D : ulift B → Sp の実錐の構成へ至る接続の設計・見積もり。空間の HasColimit から Sp の HasLimit は直接には従わず、その接続は未構成。既存の通常小図式の極限を再実装しない。
- d3 の再開条件は未成立：foundations.md では I-b の F1b-7・N-2・K-5〜K-8 等が未完。I-b 末尾までは evaluationPost circle・逆関手案・IsStable の実装へ戻らない。

## K-5：K-基盤 1 の抽象部分（2026-10-20）

- **分担**：本レーンは `KST/LocalizingInvariants/` と専用集約・監査を所有する。K-S• は SConstruction の構成・具体的 K 関手との接続を担当し、本レーンでは読み取り専用。F3 の IsStable・IsExactFunctor と D の β3 を変更しない。
- **対象・射**：StableCategory は小さい安定 quasicategory、ExactMap は F3 の完全関手。exactFunctors は内部 Hom の完全な頂点による充満部分 ∞ 圏。これを core 化した Hom の単体的圏の coherent nerve を構成する。冪等完備化は後続の Cat^perf 界面で別条件として扱う。
- **提供済み宣言**（共通接頭辞 `KST.LocalizingInvariants`）：StableCategory、ExactMap、exactFunctors、exactFunctorVertexEquiv、StableQCat、StableInfinity、stableInfinity_quasicategory、stableObject、stableVertex、stableArrowEquiv、IsVerdierSequence、VerdierSequence、IsVerdierSequence.universal、inverts_iff_kills_inclusion。
- **Verdier 列**：完全関手 i : A → B、q : B → C、i の充満忠実性、q の核と i の本質像の一致、cofiber が i の本質像に属する辺に関する q の局所化普遍性を要求する。D が Drinfeld 商を後から具体例として接続する。単なる核の一致を商の普遍性の代用にしない。
- **局所化不変量**：実際の Sp 値 ∞ 関手が Verdier 列を実 fiber 四角形に送る条件を定義する。Sp の IsStable は使わない。全整数 π の長完全列、同値検出、切断を持つ fiber 列の積分解を証明する。filtered 余極限保存等は必要な追加条件として区別する。
- **追加の提供済み宣言**：VerdierDiagram、IsZeroCategory、PreservesZeroCategories、IsLocalizingInvariant、LocalizingInvariant、IsLocalizingInvariant.fiberTriangle_isFiber、value、valueMap、valueHomotopyGroup、valueHomotopyMap、value_isInvertible_of_piIsomorphism、SplitFiber.section_map、SplitFiber.boundary_eq_one、SplitFiber.inclusion_injective、SplitFiber.groupEquiv。
- **今回の提供済み宣言**：zeroCategory、zeroCategory_isZero、toZeroCategory、fromZeroCategory、isExact_of_zero_values、verdierZeroCompositeIso、exactMapCoreVertexIso、stableArrow_homMk_eq_of_functorIso、exists_verdierSquare、VerdierSequence.presentation、VerdierSequence.presentation_sequence、IsLocalizingInvariant.abstractFiberTriangle、IsLocalizingInvariant.abstractFiberTriangle_isFiber、IsLocalizingInvariant.abstractFiberTriangle_bottom、IsLocalizingInvariant.abstractFiberTriangle_right、FiberDetection.piIsomorphism_of_fiberGroups、FiberDetection.piIsomorphism_iff_fiberGroups、FiberDetection.isInvertible_of_fiberGroups。
- **BF fiber の追加界面**（接頭辞 `FiberModel`）：obj、inclusion、comparison、comparison_inclusion、comparison_isInvertible、pointedCone_isLimit、infinityCone、infinityCone_isLimit、replacedCone、replacedCone_vertex、replacedConeComparison、replacedConeComparison_projection、homotopyFiberCone、homotopyFiberCone_isLimit、homotopyFiberCone_vertex、homotopyFiberSquare、homotopyFiberSquare_vertex。raw fiber の極限性は各段の実際の pointedFiber の普遍性から証明。置換後の図式上では、比較射上の slice の辺も保持する。
- **今回の追加界面**：StrictConeTransport.transport・apexEdge・diagramEdge、FiberModel.homotopyFiberTransport・homotopyFiberLeg_left_hom・homotopyFiberSquare_bottom_edge・homotopyFiberSquare_bottom_hom、SpectrumHo.component_eq_of_hom_eq・homotopyMap_eq_of_hom_eq・piFunctor・piComparison・piComparison_naturality、CoherentSplitFiber.section_map・boundary_eq_one・inclusion_injective・groupEquiv。錐の輸送には元の厳密自然変換の全 prism を使い、各脚を元の BF 射へ戻す。
- **未完・依存順**：一般 Sp fiber 四角形への長完全列の移送、coherent な切断付き列の Sp 積同値（暫定 8–24 時間以上、上限保証なし）。元の BF fiber 四角形の下辺の類と包含の照合、h Sp 上の π 関手と BF π との自然性は完成。CoherentSplitFiber.groupEquiv は h Sp で切断を持つ BF 射の各整数次数の群同型までで、Sp の積同値ではない。原典は HA §§1.1–1.3、BGT §§5・9。K-5 全体は未完。

## 範囲と所有

- 作業場所：`SerrePositivity/KST/Spectra/`、namespace `SerrePositivity.KST.Spectra`。
- 集約入口：`SerrePositivity/KST/Spectra.lean`、監査：`scripts/audit_kst_spectra.lean`。
- 共有ルート・他レーン・既存 Spectra/・HomotopicalAlgebra/・InfinityCategories/ は読むだけ。
- 既存の未コミット変更を保存し、他者の新規ファイルをコミットしない。
- 全体の正本は [foundations.md](../foundations.md)、K の正本は [経路](../k-theory-kst-route.md) §13。
- H_* と pro の旧レーンは凍結。γ3・γ4 は N 所有。K の合流は K-基盤レーンが担当する。

## 実装仕様

- Kan 複体の π_n は PtSimplex と RelStruct の商。零次数は pointed set、正次数は群、二以上は可換群。
- fiber と長完全列は実際の Kan fibration の充填から構成する。
- Sp は BF cofibrant–fibrant 型の Ω スペクトルの単体的圏の coherent nerve（γ-B）。
- 構造写像 ΣX_n → X_(n+1) は単射、随伴は全基点で π_* 同型。厳密な Ω 同型を要求しない。
- 写像空間は有限切断の Hom の fibration の塔の極限。指数・引き戻し・塔の相対 RLP で Kan 性を示す。
- π_j は十分高い段の π_(j+k)(X_k) と遷移同型で定義し、整数次数の自然性を保つ。
- 置換は写像柱・境界セル分解・AnodyneKanReplacement の実構成。
- 有理化は正整数の乗法の telescope と π_* のテンソル比較。
- Tot・hG は段ごとの Kan 模型。通常の Tot と BF 置換した homotopy Tot の比較を分ける。
- 値域界面は上表で固定する。IsStable はユーザー指示により I-b 末尾へ延期する。
- cohomology 消滅だけから塔の収束や Shapiro 全射性を主張しない。
- coefficientDifferential の同定は零性だけでなく像と符号も比較する。

## 原典

| 対象 | 原典 |
| --- | --- |
| Kan、π_n、群の演算、fiber 長完全列 | Kerodon §§3.1–3.2、Goerss–Jardine I §§7–8 |
| セルの係数・正規化・塔の収束 | Goerss–Jardine III §2、VIII §§1–2 |
| 通常の Tot | Goerss–Jardine VII §4、VIII §1 |
| coherent nerve | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| BF 模型 | Bousfield–Friedlander 1978 §2、HTT A.3.3 |
| Sp と ∞ 極限の比較 | HTT 4.2.4.1、HA §1.4.2 |

原典の主張を公理や未証明の入力構造にしない。未確認の定理番号は節番号で示す。

## 検証と保存

- 保存単位ごとに `lake build SerrePositivity.KST.Spectra` と専用公理監査。
- 許容公理は `propext`・`Classical.choice`・`Quot.sound` のみ。私有宣言と推移的依存も監査。
- 主経路の宣言の型に `HomotopicalAlgebra.ModelCategory` がないことを Lean 環境走査で確認。
- `ModelCategory SSet`・cofibrant generation・Quillen bifunctor を主経路の仮定にしない。
- KanQuillen の import は不可。Mathlib のホーン生成射・Fibration API は使用する。
- 工程区切りで全体ビルド。自分の import 閉包の破損を他者の修正で迂回しない。
- `git diff --check`。コミットは所有ファイルだけを `git commit --only`。amend・rebase・reset はしない。
- 本文 300 行以内、引き継ぎ 100 行以内。実施記録はコミットメッセージ。
- 旧本文・型一覧は [archive/L9-spectra-log.md](../archive/L9-spectra-log.md) に保存。
