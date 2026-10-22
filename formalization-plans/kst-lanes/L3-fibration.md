# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使い、Verdier 列 D → C → C/D に対する連結 K の fiber 列を証明する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）
### 現在地
- 工程 (a) 完了。`IsVerdierSequence` の核条件から包含の本質像と安定閉包を同定。
  cofiber の W 条件と商の可逆性、実二対三・押し出し・引き戻し・ホモトピーに対する拡大安定性を証明。
- 工程 (b)：相対図式の全単体・W 判定・内ホーン充填・再添字・core 包含を構成し、
  商の core の逆像と同定し、wS•C・商への自然変換・核の四角形へ接続。核側の全相対 S_n は弱可縮。
- W 辺と E(C,C,ker q) の元の射影は trivial Kan。K-1 で正の全有限反復の加法性を証明。
  全ての面・退化は完全で、StableModel 値の単体的対象と各段の反復実現を構成済み。
- 初期頂点と全連続辺の cofiber から、空列を含む有限 W 列の実現と積との比較を構成済み。
  零長は厳密同型、全長・全正反復は局所化同型。全単体的な有限積比較の自然同値は未主張。
- 二辺の内ホーン制限は trivial Kan。元の両短辺の厳密引き戻しと Quillen A で全 S_n・全多重対角へ接続。
- 長い単体を先行 Δ[n+1] と最後の Δ[1] の共通頂点で貼り合わせ、包含は inner anodyne。
  core 値の厳密貼合せで W 条件を反映し、制限は trivial Kan fibration。
- 元の S_n(W 列_m) の頂点と wS_n(B) の実 m 単体を、内部 Hom の交換で厳密に同定。
  全零対角・実押し出し・W 条件と全面・全退化を保つ二重単体・対角の厳密同型と K-1 object/core 比較で、
  相対 S の対角 → W 列の core S 実現の対角の実際の比較射が局所化同型と証明。
  零長同型の逆と元の退化で全定数 W 列を構成。全単体作用素・完全関手と厳密に可換で全頂点を回収。
- 元の Verdier 包含を実核部分圏へ制限し、元の写像空間の充満忠実性と核条件から完全な同値を構成。
  包含を通る合成の核は元の包含側の圏と厳密同型。核への後合成は全正有限反復で局所化同型。
  全 cofiber の後合成の自然同型から、全長・全正反復の有限積比較の後合成等式を局所化で証明。
  核係数の有限積同型と実射対の厳密な立方体で、元の初期評価四角形は homotopy pullback。
  全面・全退化を合成し、K-2 Segal 実現で全行と対角の元の四角形も homotopy pullback。
  零行同型で定数包含へ移し、object/core の厳密比較で元の相対 S 核四角形の実現も同じ性質。
  包含側の全相対 S_n の零対象の収縮を対角へ送り、一点への元の射は局所化同型。
  元の S₀ の零対象で基点を指定し、相対 core 包含の実 homotopy fiber と core S(D) の局所化同型を構成。
  同じ fiber 射影との合成は元の Verdier 包含の実現射を回収。商の core S との実 fiber 比較も構成。
  商実現射影の局所化同型性を明示的に入力すれば商 fiber 同型と同じ射影式を得る。この入力は未証明。
- 元の W cospan に普遍 Ore pullback を構成し、全図式射影は trivial Kan fibration。
  任意の部分族を固定した全境界の相対延長と、全パラメータの選択空間の contractible Kan 性を証明。
  元の固定終点 span への W 分母の cartesian lift を構成し、全辺が W である底図式上で両側 fibration。
  元の各 W 辺上で指定した実 span 輸送は、亜群化後に単体的ホモトピー同値。
- 全辺局所化の単位を全 Kan 標的で検査し、厳密な関手的 Kan 模型との実同値を証明。
  span の全単体圏上の coherent な空間値図式を構成。各値は元の両端固定分数の亜群化と同値。
  strict section の元の評価 prism で初頂点辺を反転し、同じ coherent 図式を元の底へ降下。
  両側区間 prism により W の全逆像を反転し、全辺の厳密被覆と制限同型で底上の W 反転も証明。
  元の全充満像を小さい宇宙へ縮小して商の全関手 ∞ 圏の普遍性を適用し、同じ図式を商へ降下。
  底・全単体圏への制限同型で元の strict Kan 分数値を回収。span 側の表現可能性は未証明。
- 元の全 span 族から商の coslice への実評価を構成し、元の可変終点を全単体で厳密に被覆。
  固定 fiber では既存の分数評価と実ホモトピーで一致し、亜群化後の元の fraction 比較も自然同型で回収。
  全 strict section 図式の自然変換と coherent な実辺を構成。全値で元の固定分数 coslice 評価と厳密に可換。
  strict Kan 写像と亜群化後の同じ評価の同値性を同定。各比較成分の同値性は既存の分数比較そのもので判定。
  二つの任意の空間値図式を共通の小さい全充満標的へ制限し、Space∞ 値の前合成の全写像空間の充満忠実性を証明。
  宇宙を揃えた全反転関手 ∞ 圏への前合成は実際の同値。同じ比較二胞体を元の商へ降下。
  coslice 側の W 反転も証明し、商上の比較の制限・実同型での正規化・実ホモトピー代表の回収式を保持。
  恒等 span の固定分数点・strict section 点・Kan 点と評価の回収式を保持。可縮な三角形選択 fiber で恒等点へ正規化。
  元の coslice fiber・亜群化後でも恒等点を回収。商上の coslice 図式は同じ射影の実分類図式と自然同型。
  同じ点を商上の span 図式の実 unstraightening fiber へ移し、coslice からの実比較と厳密な底・恒等錐の回収式を構成。
  元の商比較二胞体を全写像空間の比較で小さい底上の実写像へ移し、同じ代表辺の類と相対頂点を厳密に回収。
  coslice 単位との合成の恒等点は、同じ coherent 比較二胞体の pointed-space fiber 作用と厳密に一致。
  恒等錐評価は全写像空間で充満忠実、固定した点の延長空間は可縮 Kan。実恒等点の同型から相対三角比較を回収。
  実 coslice 辺を同じ三辺の合成三角形へ展開し、輸送した実点の矢印の類は元の点の射と底の辺の合成と証明。
  pointed 作用と指定成分の合成を同定。商・初頂点の指定値同型で native 比較像を回収し、点の射の等式を実 fiber 同型へ反映。
  native 比較の全 fiber 写像・点を元の pointedMap で回収。同じ表現空間の同時評価は元の diagramIso の指定成分そのもの。
  同じ表現比較に対し、元の pointedMap の点の射と指定 fiber の実点の射は、同じ diagramIso の指定成分との合成で比較先の点へ移る。
  分類同型の商・初頂点制限を元の section・表現・底変換で計算。可縮空間から選んだ比較・nerve の coherent transport 比較も同じ実点を保つ。
  全写像空間から作った同じ小さい実比較は可逆な二胞体を前合成同値へ送り、fiber 点の射も元の成分で計算。
  指定成分の作用を保持する pointed 復元射の底・同値性を証明。復元点の射は native 恒等点の射と分類逆成分との合成。native 恒等点の任意の同じ相対表現への比較式も回収。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列で右射影の全射性と接続射の自明性を同定。左項が連結なら零次射影は全射。十分条件は未証明。
- 対象 8639 jobs・専用監査 321 モジュール 1776 宣言・全体 24817 jobs が成功。
  標準三公理のみ、宣言型の ModelCategory・ソース・diff 検査も成功。所有 import 閉包 4899 モジュールは EInfinity を含まない。
### 残り（依存順）
1. 構成した wS•C と加法性からの連結版 fibration 定理
   （Waldhausen 1985 1.6.4、BGT §7、暫定 40–80 時間）。
2. 必要な cofinality 条件の明示。K-S• の K-1（加法性）・K-2（homotopy fiber 比較）の
   宣言だけを入力にする（BGT §7–8、暫定 16–32 時間）。
3. K(D) → K(C) → K(C/D) の fiber 列（連結版、Sp 値）。K-5 の形と π 同値検出へ
   接続する（BGT §7–8、暫定 16–32 時間）。
4. 冪等完備化と非連結化への入力の整理（BGT §9、暫定 8–16 時間。K-7 本体は別工程）。
### 主要宣言（共通接頭辞 `SerrePositivity.KST.Fibration`）
- weakEquivalences、mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、
  weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- relativeSConstruction、relativeSimplicialSConstruction、relativeSimplicialQuotientMap、relativeSimplicialKernelSquare。
- weakStringConstantPostSquare_homotopyPullback、relativeSKernelRealizationSquare_homotopyPullback。
- relativeSFibrationFiberIso、quotientSFibrationFiberIsoOfComparison（商実現比較の可逆性を入力）。
- spaceLocalizationPre_fullyFaithful、spaceLocalizationPrecomposition_isQCatEquivalence。
- weakQuotientMappingComparison、weakQuotientMappingComparison_pre_normalized、weakQuotientMappingComparisonHomotopy_hom。
- fractionKanQuotientDiagram_classificationIso、weakQuotientCosliceComparison、
  weakQuotientCosliceCompositePoint_action、weakQuotientCosliceTriangle_of_identity_hom。
- weakSpanKanMappingComparison_value、weakSpanKanMappingComparison_value_equivalence_iff、
  weakIdentityKanMappingComparisonUnitIso、weakQuotientCosliceUnit、weakQuotientCosliceUnit_identity。
- transportWitnessDiagramValueIso_eq、transportRepresentationFiberPointHom_diagramIso、nerveCoherentTransportRepresentationIso_pointHom、nativeCosliceIdentityPoint_comparison。
### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-1・K-2）、`KST/LocalizingInvariants/`（K-5）、`KST/Spectra/`、`InfinityCategories/Derived/`（β3 の Verdier 列）。
- 提供先：K-7（非連結 K）、K-基盤 2（K が局所化不変量であること）。
- 工程 (a) の直接入力は K-5 の `VerdierSequence` と Stable の実 cofiber・八面体・
  基底変更・前三角構造。SConstruction と Spectra の直接 import はない。
- 工程 (b) は F1 の `CoreKan` と、K-S• の `StructureMapCofibers` を直接 import する。
  固定界面は L1 §6。依頼先は `01a151d3-f75d-7ef2-9d1f-908c85eb1be1`。
  ClosedStablePredicate 版加法性を任意 W 辺版とせず、W の保存と比較を証明。K-3 以降は未依存。
  追加固定界面（L1 §6）：multiRealization_map_positive_localized_eq_of_functorIso（正反復）。
  RelativeCofiberLeftFiber・RelativeFiberEquivalence は L1 §6 の固定界面。K-F の基底変更と Quillen A へ接続。
- 工程 (c) の必要条件は K-5 の `NativeFiberSequence` の整数長完全列を入力にする。
  Sp の IsStable は使わない。K-3 の具体的 K 関手・π₀ 比較は未接続。
### 未コミット
- なし（同時評価の指定成分・表現比較の実点・native 恒等点の比較の6モジュール、集約・監査・本計画を含める）。
### 既知の問題
- native 実像と pointed 復元点の一致は未証明。既存 nerve directComparison の存在選択は元の復元 span との相対三角比較を保持しない。指定点の主経路には対応を保持する K-F の表現を用いる。span 側の普遍性・分数比較・cofinality・Sp 値 K-6 も未完。
### 次の一手
- relativeFunctor の前合成同値に沿う延長で、元の復元 span との相対三角比較も保持する nerve 表現を K-F に構成する。cocartesian Kan の native 実像との対応を示し、同じ表現比較の点の式で pointed 復元の恒等点へ接続する。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
