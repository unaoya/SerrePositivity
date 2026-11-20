# 読む作業の覚え書き（2026-11-20）

概念の木の二段目を作るときに、読む担当が各概念について書いた覚え書き（split/c*.json と split2/d*.json の notes）をそのまま集めたもの。重複の疑い、止めた経路の部品、幹の直しの案が、定義の名前つきで入っている。**どれも読む担当の指摘で、中身の確認はこれから。** 一回目（c）は docstring と型が中心、二回目（d）は docstring のない定義の本体も読んでいる（深さは担当による）。

## C 単体集合と ∞ 圏/ファイブレーションと straightening（c00）

KST.Fibration の 27 定義（W 辺の列、wS•、Verdier の二胞体族、安定模型など K 理論のファイブレーション定理の足場）は名前の「Fibration」で入っただけと見て K 空間と K スペクトル へ MOVE（StableModel 値のものは「S 構成の入力」、fractionKanQuotientDiagram は「Verdier 列」の方が合うかもしれない）。TwoSidedDiagram／TwoSidedGrothendieck／TwoSidedElements／Hammock の homSpace は DK の transfunctor・hammock の道具で 局所化（Dwyer–Kan）へ。projectiveFibrations は複体の射影モデル構造の fibration で 複体へ（E モデル圏/モデル圏（基本）でもよい）。relativeCosliceRestriction・cosliceRestrictionFiberMap・mappingCylinderBaseProjection は相対 coslice／relative join の側なので 結とスライス へ。TrivialKanFibration は Kan 複体の側でもよいが、射の類として左・右ファイブレーションと並べた。共変表現可能関手（covariantRepresentableInfinity・homInfinityCovariant）は米田・写像空間の側とも取れる。KST.Fibration.straighteningFirstVertexSectionChart は内容が straightening の全単体切断なのでここに残した。「（補助）cocartesian 分類の Hom 比較」は 22 定義が全て一つの証明（Cat∞ 値 straightening の Hom 比較）の中間物で、docstring が短く個々の役割は名前と型から判断した。幹の名前は内容に合っている。空間値（左ファイブレーション）と Cat∞ 値（cocartesian）の二系統が並行している。

## H K 理論/K 空間と K スペクトル（c01）

170 定義のうち 82 を MOVE にした。名前空間 KST.SConstruction に置かれているだけで K 空間・K スペクトルではないものが半分ある：(1) dgOdot・PerfectLaxQuotient・IsPerfectLocalizingInvariant は Land–Tamme の ⊙ と局所化不変量で「lax 引き戻しと双加群」へ。(2) Serre 鎖の立方体・cubical Λ・simplexHA は dg 神経の左随伴（Λ と HA 1.3.1 の単体の読み替え）で「dg 神経」へ、立方体集合そのものは「necklace と立方体」へ。Λ を独立の幹概念にする案もある。(3) dg 関手の Hom の end・Perf の dg 延長・自然な cone・gluing は B/D の dg の概念へ（dgFunctorHom など 4 件は既にファイルが DifferentialGraded/ にある）。(4) 点つき単体集合の延長・持ち上げの空間、写像円柱、Ex∞ の豊穣関手、homotopy fiber は「基点付き対象」へ。迷った所：dgKNativeValueComparison は Yoneda と固定 ν 値の比較なので「S 構成の入力」にしたが lax の側でもよい。PresentedPerfectDG の対象・作用は「S 構成の入力」、その上の BF スペクトルはここに残した（S7）。DGKappaNative… は LT の四角形の頂点上の有限 BF 構成で、lax の側に移す判断もありうる。simplicialPath（単体的対象の décalage）と AssemblyInputArrow（Hom の要素の圏）は一般の圏論だが足場として残した。閉じた安定部分圏（ClosedStablePredicate）は cofinality と相対加法性の両方で使われる。幹の名前は残った内容からは「S 構成と K スペクトル」が合う。

## C 単体集合と ∞ 圏/局所化（Dwyer–Kan）（c02）

名前空間は Kerodon…Localization だが中身の大半は Dwyer–Kan の三論文（自由解像・hammock・モデル圏の関数複体）で、Kerodon 6.3 の普遍性は 4 定義だけ。Project.HomotopyDiagramComparison の specifiedCocone…・partialColimit…（27 件）は ∞ 圏の指定余錐と Hom の族で、定義の内容は「極限と余極限」なので MOVE にした（使い道は HA 1.3.4 のモデル圏の局所化が余極限を持つことの証明らしく、用途で分けるならここの「モデル圏の局所化との比較」に戻す）。空間値図式の積・Kan の積は「空間・Cat∞・前層・Ind」へ、cosimplicialHom は E のホモトピー関数複体へ、DGGeneratedHomWord は dg 圏へ MOVE。simplexAttachmentBoundary（join の部分複体、導来圏の局所化の線型図式の延長用）の行き先は自信が薄い。TerminalReplacement・InitialReplacement（前向き射列の同時引き戻し・押し出し）はモデル圏の分数計算用なので三本矢の側に入れた。補助 2 つは DK の計算の足場で件数が多い（合わせて 45）。

## G スペクトル/Ω スペクトル（Bousfield–Friedlander）（c03）

全て名前空間 KST.Spectra だが、内容は (a) スペクトルそのもの、(b) 点つき単体集合の一般論（path・loop・fiber・cofiber・点つき内部 Hom）、(c) loop 関手の随伴を示すための足場に分かれる。(b) の二つの小概念（点つき空間の loop・path・fiber・cofiber／点つき写像空間と区間族）は幹の「C 単体集合と ∞ 圏/基点付き対象」「写像空間」に移す候補だが、スペクトルの証明のために作られたものなので今回は MOVE にせず残した。（補助）の二つは docstring が一行で前後の構成を指す形（「元の…」「同じ…」）が多く、名前と docstring だけで分けた（AdjointLoopRelativeBF・D3…・kanAdjoint…・CotensorCompatible の区間は随伴の比較、LoopExchange・SignedAdjointPaths・CirclePower・三角形や正方形の貼り合わせは円の交換と符号）。PushoutCube・ThreeEdgeTransport・SquareAdjustment・CoherentPathCoordinates はスペクトルと無関係な単体集合の組合せで、「円の交換と符号」に入れたのは使われ方からの推定。Tot・重みつき end・塔の Milnor 比較は幹の「E モデル圏」や「極限と余極限」に近い一般論だが点つき Kan 複体に特化しているので残した。SkeletalCellAttachment（骨格のセルごとの係数）は「点つき写像空間と区間族」の骨格の塔に付けた。mathlib.txt は 4 宣言だけなので規則なし。

## F オペラドと E∞/Barratt–Eccles と全射オペラド（c04）

(1) 幹の名前より範囲が広い：BF のオペラド（E・χ・TR・余作用）は宣言の半分ほどで、残りは BE 模型による E 代数のホモトピー論（モデル構造・写像空間・ホモトピー極限）、CAlg_R、加群。幹を「BE/χ オペラド」と「E∞ 代数の圏 CAlg（BE 模型）」に分ける余地がある。(2) normalizedFunctor・linearization は一般の単体集合の正規化鎖なので B/単体的鎖とシャッフル へ MOVE とした。ShufflePath も一般の (p,q) shuffle だが BE の合成のためだけに使うので残した（B 側と重複していないか要確認）。(3) CarrierDiagram.projectiveModelCategory（複体の図式の射影モデル）と constantDiagramReplacement は E/図式のモデル構造 寄りだが、E 代数のホモトピー極限の計算のためなので残した。(4) BinaryTensorWord（二色のテンソル冪の分解）は一般のモノイダル圏の話で Z/モノイダル圏 寄りだが、HA 3.2.4.7 の余積の比較専用なので CAlg に入れた。(5) 区間切断（Δ¹）と単体切断（一般の S）は同じ BF §2.2 の公式の二つの実装で、一つの小概念にまとめた（区間版は一般版の特別な場合で、重複の候補）。(6) rowStart・canonicalRow は BF §1.4.2 の標準置換で、TR 本体に入れた。(7) StoppedRoutes.ISW2Tot は止めた経路の保管なので補助として独立させた。(8) mathlib.txt は 0 件なので規則なし。

## B 複体と dg 圏/複体（c05）

mathlib_rules は「宣言の主張に現れる Mathlib 定数のどれかが正規表現に当たれば」という読みで書いた（上から順、最後は受け皿）。c05.mathlib.txt は出現 110 回以上の定数しか載っていないので、規則は見えている定数（DerivedCategory 195、GradedObject/curriedTensor 110〜134、HasHomotopyCofiber 123、Discrete/AddCommGrpCat/forget₂ 150〜200、ComplexShape.down 359、homology/ShortComplex 150〜300）と一般的な Mathlib の名前から作った。実際の全定数で当て直して受け皿の大きさを確かめるのがよい。 HasBinaryBiproducts は写像錐の instance 引数としてほぼ HasHomotopyCofiber と同数現れるので写像錐の側に入れた。 核 79 件のうち 17 件（ComplexLimits.normalizedTensor*・ConeHeadIndex など）は N_dg(Ch) の中の写像空間・錐の計算の足場で、複体そのものの概念ではないので（補助）にまとめた。幹では「C/dg 神経」か「D/導来 ∞ 圏」の下に置く方が自然かもしれない。 係数拡大（baseChange 73 宣言）は幹の「B/係数の取り替え」と重なる可能性がある（そちらの中身を見ていないので MOVE にせず小概念にした）。 complexOrdinaryDerivedSource・kProjectiveDerivedSource は導来 ∞ 圏への写像なので MOVE、局所コホモロジー 2 件は「台つきの加群と Tor」へ、Cosimplicial の private abbrev 2 件（chains Δ[N]）は「単体的鎖とシャッフル」へ MOVE。 c11 から余単体的・単体的複体の全複体（productTotalFunctor など 14 件）をこの概念へ MOVE しており、受け側の小概念は「二重複体と全複体」「ホモトピー極限の模型」になる。

## C 単体集合と ∞ 圏/極限と余極限（c06）

MOVE 5 件：IsExactFunctor（完全関手、安定 ∞ 圏）、Sheaves.weightedSections（前層の反対 Yoneda に沿う右 Kan 拡張、HTT 5.1.5.6、∞ 層）、LeftTransportRepresentation とその 2 つ（left fibration を空間値図式で表現するデータ、Kerodon 5.6.5、straightening）。迷った所：(1)「複体の strict な図式とその ∞ 局所化」(11 件) は内容としては導来 ∞ 圏の図式圏の模型（HTT 4.2.4.4 の加群版）で、「D 導来 ∞ 圏」へ移す案もある。ホモトピー余極限の比較の入力なのでここに残した。(2)「ホモトピー引き戻し・押し出しと塔の極限」は単体集合の圏での話（Kerodon 第 3 章・Segal）で、「Kan 複体とホモトピー群」寄り。(3)「simplicial replacement」は Kerodon では第 5 章（ファイブレーション）の節だが内容はホモトピー余極限の模型。HomologicalAlgebra.simplicialReplacement（一般の圏の余積による版）も同じ小概念に入れた。(4) coherent な錐の切断空間（coherentCone*）は Kerodon 7.4.1.6 と 7.5.4.6 の両方で使われ、「空間値の図式の極限と切断空間」に入れた。(5) rightFibrationHom*・relativeSection* は fibration の言葉で書かれているが空間の極限の証明の部品として残した。(6) Initial/TerminalBoundaryLifting は相対始対象・終対象の判定条件で、「始対象・終対象と相対余極限」にまとめた。幹の名前について：始対象・終対象はこの概念に含まれている（Kerodon では 4.6.7）。

## C 単体集合と ∞ 圏/単体集合（基本）（c07）

規則は assign.py の Mathlib の定義の段と同じ使い方を想定：宣言の主張に現れる各定数を上から当て、当たった規則の番号の最小のものに入れる。確かめは work/decls.pkl（trunk3.pkl と X.pkl から抜いた 6,103 宣言）で行い、件数は notes の末尾。SSet・SimplexCategory.smallCategory・Opposite・tensorObj より上の一般的な定数は決め手にしていない（tensorObj と直積の射影は下の方で「積」に入れる）。CosimplicialObject.δ/σ は stdSimplex の余面写像として現れるので「標準単体」に、WidePullbackShape は pullback の展開なので「極限」に入れた。受け皿の 933 は主張が SSet と射だけの定義で、本体（値）を見ないと分けられない。「鎖複体と Dold–Kan」は幹の B「単体的鎖とシャッフル」、「anodyne…」は E「単体的モデルと anodyne」、「単体的豊穣」は C「単体的圏と coherent 神経」、「辺・合成・神経」は C「準圏（基本）」「神経」と範囲が重なる（Mathlib の定義だけで書かれた補題がここに落ちている）。 確かめた件数：鎖複体と Dold–Kan 対応 192、anodyne 射・リフト性・Kan–Quillen モデル構造 391、単体的ホモトピー・π₀・ホモトピー圏 189、非退化単体・骨格・切り詰め・細分 245、関数複体（内部 Hom）と単体的豊穣 450、反対単体集合と宇宙の持ち上げ 341、ホーン 333、部分複体と境界 352、積・柱・pushout-product 653、辺・合成・神経 262、単体的対象・余単体的対象・Čech 神経 462、極限・余極限・要素の圏 558、標準単体と米田 306、単体圏 Δ と単体の面・退化 436、（その他） 933。

## A 可換代数と数論幾何/環と加群（その他）（c08）

規則の使い方は c07 と同じ想定（当たった規則の番号の最小）。CommRing・Algebra・Ideal.Quotient の instance・Fact (Nat.Prime p)・AddMonoidAlgebra.semiring（MvPolynomial の展開）・OreLocalization.oreSetComm は決め手にしない。Ideal・Submodule・LinearMap は一番下の二つの規則でだけ拾う。順は「特殊な対象（分冪・Witt・微分・スペクトル・完備化・次元）→ ModuleCat → 局所環・体 → 局所化 → テンソル → 多項式 → 有限性 → イデアル → 加群」で、二つ以上に当たる宣言（例：Localization.Away のテンソル積）は上のものに入る。多くの小概念は幹の A の別の概念の Mathlib 側の補題（分冪代数→「分冪包絡とクリスタリン」、Witt・tilt→「パーフェクトイド」「δ 環」、完備化・Rees→「Rees 代数と進完備」「導来完備化」、外積代数→「Koszul 複体」、Kähler 微分→「de Rham 複体」、長さ→「正規化長さ」、根の添加→「根の添加（André）」）で、そちらへ移す候補。 確かめた件数：分冪代数 276、Witt ベクトル・tilt・Frobenius と標数 p 438、導分・Kähler 微分・外積代数 269、素スペクトル・Zariski 位相・層 321、フィルター・次数付き環・I 進完備化 520、次元・長さ・正則列 260、加群の圏とホモロジー代数 771、局所環・剰余体・体の拡大と整拡大 354、局所化 275、テンソル積・底変換・平坦性 379、多項式環と冪級数環 292、有限性・Noether 性・自由加群 154、順極限・直和・環の圏の（余）極限 185、イデアル・剰余環・環準同型 491、加群・部分加群・線型写像 191、（その他） 301。

## H K 理論/局所化不変量：Postnikov と平方零拡大（c09）

MOVE は 0 件。全て KST.LocalizingInvariants の dg 代数（Mon (Complex R)）の話で、Land–Tamme §2 の「k-connective な局所化不変量は Postnikov 塔・平方零拡大で決まる」議論の dg 増強版。docstring はほとんど無く、名前・signature・ファイル冒頭の概要で判断した。胞体分解・path 対象・ホモトピー引き戻し・写像空間（T1〜T3・T7、計 44 定義）は Postnikov に固有でない dg 代数のホモトピー論で、幹「D/dg 代数（一対象 dg 圏）」（18 宣言しかない）と合わせて一つの幹「dg 代数のホモトピー論」にする案がある。今回は使われ先がここだけなので残した。170 定義のうち 53 が帰納の足場（T10・T11）で、同じ構成の PostnikovCommonCore 版と二切断（Two / postnikovCommon…）版が並ぶ：後者は前者の n=1 特殊化の別名（abbrev）が多く、言い換えの整理候補。postnikovStrictZeroBase・postnikovFiniteDiagonalTarget・PostnikovImagePro.middle は類の表示（T6）と pro 逆（T9）の境目で、pro 逆の側に入れた。

## C 単体集合と ∞ 圏/結とスライス（c10）

準圏の随伴（Kerodon §6.2：QCatAdjunction、単位・余単位、unit comma とその fiber、各点の単位条件）の 29 定義がこの概念に入っていたので 随伴（2 圏）へ MOVE。受け側は今 60 宣言しかなく、名前を「随伴（∞ 圏）」のように広げ、小概念は「随伴の定義（h Fun の 2 圏）」「unit comma と普遍矢印」「各点の単位と写像空間条件」に分かれる見込み。区間写像空間の操作（intervalFunctorMap・intervalPre/Postcompose・intervalFamilyHom/Homotopy）は随伴の証明用だが内容は写像空間なので 写像空間へ。localEquivalences（HTT 5.5.4.1 の S 同値）は Bousfield 局所化で、幹に合う概念がないため最も近い 局所化（Dwyer–Kan）とした。PointedObject.adjoin（基点の追加）は名前の join で紛れたもの。KanEnrichedDiagram.jointEvaluation、ZigzagMovingDiagramParts.jointFunctor も同様（joint）。nerveVertex・nervePoint は神経の一般的な定義なので 神経へ、mapJoinCone・mapJoinCocone は錐の後合成なので 極限と余極限へ。join の結合同型が二つ（stableJoinAssociator と joinAssociator）、切断の表示も二系統（StableAugJoin と joinSumSimplex／joinTripleSimplex）あり、重複の候補。cosliceTwistedArrowMap は ねじれ矢と余スパン、sliceOverCorner は導来 ∞ 圏の補助とも取れるが、coslice／slice の構成としてここに残した。

## B 複体と dg 圏/導来圏と Perf（dg 加群）（c11）

幹のこの概念には、名前に Perfect/perfection を含むだけで dg 加群と無関係な定義が 30 件入っている（名前でハブを延ばした結果と思われる）：Bhatt–Scholze の Semiperfectoid・δ 完全化・perfectoid 化・PerfectPolynomial など 26 件は A の各概念へ、環上の狭義 perfect 複体 4 件は「完全複体と K₀」へ MOVE した。Semiperfectoid.* の行き先（パーフェクトイド／プリズム／根の塔／根の添加）と、δ 完全化・PerfectClosure の行き先（δ 環／Frobenius の順極限）は名前と docstring だけで決めたので要確認。 核 165 件の3 分の 1 強（59 件）は HA/DerivedCategoryModels/CoherentBar ほかの coherent bar 構成で、「導来圏と Perf」というより「dg 神経の中のホモトピー余極限の計算」。幹で独立の概念（例：D/導来 ∞ 圏の余極限、または C/dg 神経の下）にする方がよいかもしれない。ここでは本体 1 つと（補助）3 つに分けた。 余単体的・単体的複体の全複体（Tot・BK 重み、11 件）と複体のホモロジーの補助 3 件は複体だけの話なので「B/複体」へ MOVE（c05 の「二重複体と全複体」「ホモトピー極限の模型」に入る）。N_dg(Ch) の標準 cofiber 四角形、h D(S) と導来圏の比較、環 S の Perf(S)・Perf_Z の ∞ 圏模型は「D/導来 ∞ 圏」へ MOVE（Perf(S) は「H/S 構成の入力」でもよい）。 dgModulePerfectInfinityCategory など dg 加群の Perf の dg 神経 3 件は残した。StrictPerfectDGComplex は dg 増強に入れた。bimoduleToDerived は双加群の導来圏の局所化関手なので c22 へ MOVE。

## B 複体と dg 圏/dg 加群（c12）

核は 34 件と少なく、内容はそのまま Keller の順に分かれた。導来圏への局所化関手 moduleHomotopyToDerivedClosed と左加群の導来圏 DerivedLeftModuleCategory は「導来圏と Perf（dg 加群）」へ MOVE。 幹の区切りとして、K(D)・擬同型・ホモトピー射影性はこの概念、D(D) は c11 という線になっている（moduleQuasiIso はここ、その局所化は c11）。半自由加群・cell は「dg 商と cell 分解」にあると思われる（この核には無い）。

## E モデル圏/ホモトピー関数複体と分解（c13）

170 定義のうち 125 が「中断した任意モデル源への一般化（計画書 §396、分類 B）」の足場で、docstring がほとんどなく、ファイルの見出しと署名から分けた。完成した数学として読めるのは 余単体的分解と frame／ホモトピー関数複体／実現とテンソル／余モナドの分解と自由な道の圏 の四つで、残り（持ち上げの空間、bar 構成、二つの（補助）、frame と hammock の比較）は一つの未完の厳密化の議論の部品。DGModuleFunctorResolutionObject（418 宣言で最大）は dg 関手の半自由分解の対象で、名前の Resolution で紛れ込んだもの：B 複体と dg 圏/導来圏と Perf（dg 加群）へ MOVE（導来 Hom の構成なので D 安定 ∞ 圏と導来 ∞ 圏/導来 ∞ 圏 でもよい）。余モナドの分解と自由な道の圏（FreePath・FreeGenerator・ComonadResolutionOperators、ファイルの分類 A）はモデル圏と無関係な一般論で、幹の「Z 圏論一般/圏・関手・極限」か「C 単体集合と ∞ 圏/局所化（Dwyer–Kan）」に移す候補。frame の Hom と hammock 局所化の比較 も「局所化（Dwyer–Kan）」と境界が接する。ResolutionArrowDiagram は持ち上げの空間の図式として「持ち上げの空間」に、その境界・端点・組の整合（CylinderBoundary・ComparisonEndpoints・TupleCoherence）は（補助）に分けた。local instance（ResolutionLiftSpace.instModelCategory…）は Reedy モデル構造の局所 instance で、定義というより設定。mathlib.txt は 0 件。

## C 単体集合と ∞ 圏/dg 神経（c14）

「複体の標準 fiber と引き戻し四角形」とその補助は、複体の dg 神経（導来 ∞ 圏の模型）での有限極限の話で、幹の「D/導来 ∞ 圏」または「D/安定 ∞ 圏」（c21 の複体の cofiber 四角形と対）に置く方が自然かもしれない。「Dold–Kan の Hom 空間」「Alexander–Whitney 合成」は幹の「B/単体的鎖とシャッフル」と内容が重なる（標準模型は Mathlib の Γ と別に作ってある）。「（補助）立方体・旗・Path の評価」は幹の「C/necklace と立方体（組合せ）」と近い。dgModuleAugmentationCutPoints（相つきの切断点の有限集合）は名前は dg 加群だが切断点の組合せなのでテンソルの補助に入れた。dgNerveCommonMap は Functor.map の宇宙持ち上げ版（言い換えに近い）。

## C 単体集合と ∞ 圏/Kan 複体とホモトピー群（c15）

この概念は寄せ集めに近い：本体は（ホモトピー群・長完全列・弱同値・Ex∞）で、残りは Project/KanComplexAuxiliaries の足場。立方体圏と生成語（ConcreteCube・CubeWords など 11 件、Serre 鎖立方体の表示非依存性のため）は necklace と立方体へ、点つき写像空間と区間（4 件）は基点付き対象へ、HomTensorStrength はモノイダル圏へ、NormalizedValueCochains は単体的鎖へ MOVE とした。「Kan 値の図式と空間の ∞ 圏への写像」は幹の「C/空間・Cat∞・前層・Ind」に丸ごと移してもよい。mathlib_rules は宣言の主張に現れる Mathlib の定数に上から順に当てる想定（mathlib.txt は定数ごとの集計だけなので、宣言ごとの共起は見ていない）。Mathlib だけの宣言の大半は SSet.Homotopy／RelativeMorphism（約 490 件）で「単体的ホモトピーと prism」に入る。HomotopyCategory・Truncated の補題（約 48 件）は本体の定義を持たない小概念「単体集合のホモトピー圏（Mathlib）」に受けたが、幹の「C/準圏（基本）」に移す方がよいかもしれない。ホーン・anodyne・rlp の補題は Kan ファイブレーションの側に入れた（「E/単体的モデルと anodyne」と境界が曖昧）。

## C 単体集合と ∞ 圏/関手単体集合と同値（c16）

MOVE 4 件：dg 双加群の射を dg 神経の間の h Fun の射へ送る関手 3 つ（dgKernelDerivedFunctorHomFunctor・dgKernelTensorFunctorHomFunctor・dgBimoduleFunctorHomFunctor；値が h Fun なのでここに来ているが内容は dg 双加群の導来作用。「D 導来 ∞ 圏」とした。「H 局所化不変量：lax 引き戻しと双加群」「B 双加群とテンソル」も候補）、strictKanCompletion（厳密に関手的な Kan 置換、Kan 複体の側）。迷った所：「fiber ごとの関手の全空間」は Kan 拡張の相対 join の証明で使う構成で、「極限と余極限」の Kan 拡張に寄せる案もある。「∞ 圏のホモトピー引き戻し」は「空間・Cat∞」寄りだが path 置換と一体なので残した。「可逆な区間と円柱」は同値の判定の道具。幹の名前について：この概念は「関手単体集合（Fun と h Fun）」と「同値（同型・core・path 置換）」の二つの塊からなる。

## C 単体集合と ∞ 圏/空間・Cat∞・前層・Ind（c17）

dg 加群から 𝒮 への関手 3 件（dgBar…・dgHom…UnderlyingSpaceInfinity）は導来 ∞ 圏へ MOVE。「（補助）錐・余錐の輸送と変換」（12 件）は内容としては「極限と余極限」の道具で、Cat∞ の引き戻しと前層の密度の証明のために置かれている。arrowBoundary（区間の二端点、Tamme の lax pullback 用）もここに入れた。P_Σ はこの概念に 2 件、c25 に Yoneda・評価が 5 件あり、c25 の分はここへ MOVE とした。Ind は 2 定義だが宣言の数は最大（763）。

## D 安定 ∞ 圏と導来 ∞ 圏/dg の貼り合わせ（c18）

158 件のうち約 90 件は一つの比較定理（貼り合わせの dg 神経と ∞ 圏の lax 引き戻しの同値、Hom 複体と lax 写像空間の比較）の足場で、docstring のない定義が多い（ファイル先頭の説明で判断した）。足場は「合成対応と入力 fiber」と「単位補正・正規化の族」の二つの（補助）に分けたが、境界ははっきりしない。数学の概念として立つのは最初の 6 つ。幹の「H/局所化不変量：lax 引き戻しと双加群」と範囲が重なる（「安定 ∞ 圏としての貼り合わせと lax 引き戻しとの比較」はそちらの入口）。BoundaryGluing.StandardCompatible（境界の面の恒等式）は単体集合の基本なので MOVE。Milnor 四角形は dg 代数（「D/dg 代数（一対象 dg 圏）」）や K 理論の切除と近い。

## Z 圏論一般/組合せと順序（c19）

規則の使い方は c07 と同じ想定。Nat・Fin・Eq・LE.le・Finset の instance は決め手にしない。OrderHom・Fin.succAbove などは代数・リスト・鎖より下、Finset より上に置いた。受け皿 244 は Nat・Int・Fin の算術だけ。「代数・解析の初等補題」（269）は幹の A「環と加群（その他）」に近く、「置換と Coxeter 群」「リストと語」は大半が F「Barratt–Eccles と全射オペラド」の足場、「Fin の単調写像と単体圏」は C「単体集合（基本）」「dg 神経」の足場（file で見ると EInfinity・Kerodon/Examples・DerivedCategories が多い）。 確かめた件数：置換と Coxeter 群 209、箙・道・全域木 87、基数・順序数・整礎性 72、Fin の単調写像と単体圏 575、符号・二項係数・有限和 137、代数・解析の初等補題 269、リストと語 161、半順序・鎖・区間・束 282、有限集合・写像・数え上げ 388、（その他） 244。

## C 単体集合と ∞ 圏/写像空間（c20）

MOVE なし。迷った所：(1)「dg 神経の写像空間（線形模型）」(18 件) は「C dg 神経」へ移す案がある。写像空間の具体的な計算なのでここに残した。(2)「錐の関手空間と太い slice」は内容としては「結とスライス」（fat slice）や「極限と余極限」（錐の族、c06 の coconeFamily・coconeRestriction と左右対称）に近い。c06 の「余錐の空間」と同じ場所にまとめる方が自然。(3)「矢印の空間と lax 引き戻し」の laxPullback* は K 理論（Tamme の lax pullback）の入力で、「H 局所化不変量：lax 引き戻しと双加群」の ∞ 圏側の定義にあたる。MappingArrowComparison・leftMappingArrow は随伴の写像空間の比較の準備。(4) internalHomFlipHomEquiv は c16 の internalHomSwapIso・transposeFunctorFamily と同じ内容（重複の候補）。

## D 安定 ∞ 圏と導来 ∞ 圏/安定 ∞ 圏（c21）

「安定性の判定」は 46 件と最大で、ほぼ全部が一つの証明の足場（添字の順序集合、穿孔格子、貼り合わせ）。その中の posetSubtype*（順序部分型の神経）、binaryPoint*（離散二点図式）、LeftFibrationFiberTransport は一般の道具で、それぞれ「C/神経」「C/極限と余極限」「C/ファイブレーションと straightening」に置けるが、ここの証明でしか使われていないようなので補助に残した。Verdier.* と RelativeVerdier*・cofiberLocalizingEdges・relativeFunctorCore（10 件）は幹の「D/Verdier 列」へ MOVE。KST.Fibration の *ExactMap（S• 構成の間の完全関手、4 件）は K 理論へ MOVE（行き先は「H/K 空間と K スペクトル」とした。「H/S 構成の入力」かもしれない）。PointedObject.cofiber（基点付き対象の商）は基点付き対象へ。「複体の dg 神経での cofiber 四角形」は「D/導来 ∞ 圏」に置く手もあり、c14 の「複体の標準 fiber と引き戻し四角形」と同じ所にまとめるのがよい。docstring の『HA 1.4.2.15』という番号は確かめていない。

## B 複体と dg 圏/双加群とテンソル（c22）

BimoduleTensor.compose の「合成」は双加群の相対テンソル Q⊗_C P。合成と制限の比較同型（compose*RestrictionIso、middleRestrictionComparison*）は underived のものは「双加群の合成」、導来圏のものは「導来合成と制限の両立」に入れた。 K-flat 性は複体・加群・dg 圏・双加群の四つの水準の定義が一緒になっている（complexKFlat は複体だけの性質なので「B/複体」でもよいが、使われ方が導来テンソルなのでここに残した）。rightKFlatQuasiIso・DerivedRightKFlatBimoduleCategory など K-flat 部分圏の局所化は導来合成の模型なので「導来双加群圏と導来合成」に入れた。 KFlatDGResolution（局所 K-flat な dg 圏による分解）は「dg 商と cell 分解」または「dg 圏と dg 関手」と境界が近い。 InfinityCategories/Project/DerivedCategories の 8 件（相対 K-flat 加群の dg 神経、kernel の作用の合成同型）は ∞ 圏の側の主張で、幹では「D/導来 ∞ 圏」か「H/局所化不変量：lax 引き戻しと双加群」に近い。kernel の導来作用 1 件とまとめて小概念にした。c11 から bimoduleToDerived がここへ MOVE されてくる（「導来双加群圏と導来合成」）。

## D 安定 ∞ 圏と導来 ∞ 圏/導来 ∞ 圏（c23）

核の定義は 12 件しかなく（宣言は 2312）、少数の定義に補題が集中している。そのため小概念は 6 個で、うち 3 個は定義が 1 件。IsDGPretriangulated（575 宣言）は dg 圏の性質なので幹の「B/dg 圏と dg 関手」または「B/三角圏」に、DGFunctorCommaObject（170 宣言）は「D/dg の貼り合わせ」（c18 の comma 表示）に移す手もあるが、導来 ∞ 圏の安定性と lax 引き戻しの入力として使われているのでここに残した。complexPinchedSpace は「C/写像空間」と近い。

## Z 圏論一般/圏・関手・極限（c24）

規則の使い方は c07 と同じ想定。Category・Functor・Functor.obj/map・Quiver.Hom・CategoryStruct.comp・Functor.category は決め手にしない；Iso・Functor.comp・Opposite・Discrete・Cat は最後の小概念「基本」でだけ拾い、Preorder.smallCategory はその直前で「順序集合の圏」に入れる。「モノイダル構造と豊穣」は幹の Z「モノイダル圏」「豊穣圏」、「加法圏・Abel 圏・三角圏」は B「三角圏」「複体」、「局所表示可能圏…」は C「サイズの条件」や E「語による分解」、「箙・自由圏」は Z「組合せと順序」の「箙・道・全域木」と範囲が重なる。 確かめた件数：加法圏・Abel 圏・三角圏 263、局所表示可能圏・到達可能性・基数の条件 144、射の類・充満部分圏・局所化・冪等完備 45、箙・自由圏・群と一対象圏 151、位相空間・サイト・層 44、モノイダル構造と豊穣 56、随伴・Kan 拡張・米田 86、射の圏・スライス・コンマ圏・要素の圏 487、順序集合の圏・合成可能な射の列・神経 209、極限と余極限 244、サイズと宇宙の持ち上げ 54、関手・自然変換・同型と同値（基本） 352、（その他） 101。

## C 単体集合と ∞ 圏/表現可能 ∞ 圏とフィルター（c25）

幹の名前「表現可能 ∞ 圏」は presentable の意味なので「表示可能 ∞ 圏」とするのがよい（表現可能は representable で、c17 の米田と紛れる）。IsAccessible・compact 対象の定義そのものはこの核にない（別の概念にあるはず）。P_Σ の Yoneda・評価 5 件は c17 へ MOVE、HA の安定表示可能の 3 件（stableArrowCategory など）は安定 ∞ 圏へ MOVE。Project.FilteredExchange の半分は path 引き戻しの具体模型で、filtered 交換の証明の足場。continuousLeftFibrationReplacement（左ホーン付加の可算反復）は内容としてはファイブレーション側だが、分類図式の比較の道具としてここの補助に置いた。mathlib のみの宣言は 15 件で規則は作っていない。

## A 可換代数と数論幾何/Frobenius の順極限（d00）

幹の名前は「Frobenius の順極限（余完全化 A_perf）」とすると中身が分かる。Mathlib の Perfection（逆極限）とは別物と冒頭に明記。frobeniusRingDiagram は Čech 複体の係数図式として使われ（d07 の schemePerfectCech*、d04 の projectiveFrobeniusRingChartDiagram）、使い手は「Čech 複体と被覆」側にある。

## A 可換代数と数論幾何/Hilbert–Samuel と対角線（d01）

ReesModule・GradedReesRing は幹「Rees 代数と進完備」（今は中身がほぼ空）と重なる。DiagonalRing は等標数の交点重複度（Serre の対角線への帰着）の道具で、幹「交点重複度と χ」に入れてもよい。adicSubmodule は Mathlib の I.stableFiltration ⊤ の第 n 段の言い換え。

## A 可換代数と数論幾何/Koszul 複体（d02）

Koszul 複体の模型が二つある：反復錐の koszulComplex と外積の exteriorKoszulCochain（KST、「既存 derivedChartComplex との比較」に使うと docstring にある）。Adams.oneKoszulComplex は koszulComplex (fun _ : Fin 1 => a) の略記で 202 宣言が使う；Adams.* は K 理論の Adams 作用素の計算（KTheory/Adams/）で、幹に「Adams 作用素」に当たる概念がないのでここに残した。Adams.oneKoszulUnit は R を 0 次に置いた複体で Koszul 固有ではない。koszulCompletionComplex（冪の Koszul 塔の holim）と complexPowerKoszulStage（Cone(aⁿ)）は完備化の模型なので導来完備化へ；塔そのもの（powerKoszulTower など）は Koszul に残した。LengthAlgebra.KoszulFinite・koszulEuler は幹「正規化長さ」に入れてもよい。koszulDualModuleFunctor（R 係数）と algebraKoszulDualFunctor（C 係数）は同じ構成の係数違い。

## A 可換代数と数論幾何/Rees 代数と進完備（d03）

この概念に残っている定義は無名の局所インスタンス一つだけで、Rees 代数や進完備の定義そのものはここにない。同じ族（reesAdicProjective…、I 進閉厚化 M/IⁿM）は d04「blowup と射影スキーム」に入っており、Rees 加群・随伴次数は d01「Hilbert–Samuel」にある。幹の「Rees 代数と進完備」は独立の概念として立てず、d04 の小概念「I 進閉厚化と Rees 加群の Proj 次数」か d01 に吸収するのがよい。

## A 可換代数と数論幾何/blowup と射影スキーム（d04）

この概念は実質三つの塊：(1) blowup（Rees・アフィン・貼り合わせ・純変換、KST §5）、(2) 射影空間の標準開の係数図式（Čech の係数、d07 の fullCechComplex に入れて使う）、(3) I 進閉厚化 M/IⁿM と Rees 加群の Proj 次数（形式関数、d07 の reesAdicProjective…Cech… と対）。(2)(3) は「blowup」ではなく「射影空間の連接コホモロジー（Čech）と形式関数」で、幹を分けるか「Čech 複体と被覆」側とまとめる余地がある。幹「Rees 代数と進完備」(d03) はこの (3) と d01 の Rees 加群に吸収できる。OpenAtlasModelData・atlasArrowFamily は有限表示スキームのチャートと交叉を有限生成部分代数上の模型に降ろすデータ（Noether 近似、ファイル冒頭の「G2」）で blowup でも Proj でもない；スキームへ（幹に「有限表示の極限・降下」があればそちら）。specIdealEquiv は Spec A のイデアル層と A のイデアルの順序同型（Stacks 080Y）でスキームの一般論。projectiveMonomialCochains は一つの Laurent 単項式に対応する Čech コチェインの部分加群で Čech 側。projectiveFrobeniusRingChartDiagram は d00 の FrobeniusDirectLimit を標準開に並べたもの。重複の疑い：projectiveGradedModuleChartDiagram（整数次数）と projectiveNatGradedModuleChartDiagram（自然数次数を延ばして前者に渡す）と projectiveHomogeneousChartDiagram（次数零、projectiveHomogeneousChartLinearEquiv で前者と同一視）は同じ図式の三つの表示。reesAdicProjectiveQuotientPiece / reesClosedCoefficientPiece / reesCoefficientAdicPiece は同じ商の次数成分を係数環だけ変えて表したもの。matrixMinorIdeal は幹「環と加群（その他）」でもよい。

## A 可換代数と数論幾何/de Rham 複体（d05）

de Rham 複体は多項式代数 k[T]（T 有限）の場合だけを明示的に作っている（Kähler 微分の外冪による一般の定義ではない）。幹の名前は「多項式の de Rham 複体と Cartier」とすると範囲が正確。polynomialFormsBasis は Cartier 同型の代表形式の基底（CartierWeight.lean）に使う。GradedCommDGAlgebra は幹 F「dg オペラドと代数」や D「dg 代数」とは別の、ℕ 次数・可換の専用の構造（重複の疑いとして確認の価値あり）。Poly は MvPolynomial T k の別名。

## A 可換代数と数論幾何/p 基底（d06）

名前どおりの概念で、誤って入った定義はない。pPowerSubfield は Frobenius の像（Mathlib の frobenius の fieldRange）。

## A 可換代数と数論幾何/Čech 複体と被覆（d07）

名前に Cech があるだけで別の概念だったもの 21 件を移した：プリズムの Čech–Alexander 模型（BigCechTerm ほか、BS Construction 4.17）、分冪 Čech 脈体と結晶比較（PDCechNerve.*、pdCechNerve、pdRawMap ほか）、KST の降下の二重 Čech 図式（KST.Descent.*、補題 3.2・3.3）。BhattScholze.Prismatic.Term・K・Diff・copy・pdRawMap は private な足場（Term・K は相対 Frobenius に沿う Čech 比較 FrobeniusCechComparison.lean、Diff・copy・pdRawMap は多項式の pd Čech 模型 PDPolynomialCech.lean）。幹の直し：Cosimplicial.*（余単体的可換環のコホモロジーと cup 積、10 件）は Čech 固有ではなく「余単体的環のコホモロジー」として独立させるか B「複体」寄り。「形式関数」と「射影空間の Čech コホモロジー」は d04 の標準開係数図式・I 進閉厚化と対で、まとめて一つの概念（射影空間の連接コホモロジーと形式関数）にできる。「完全化した構造層の Čech 降下」と（補助）四角形は BST13 の h 降下（完全スキームの構造層）の経路で、d00「Frobenius の順極限」の使い手。CechNerveData は BS の prismatic site 用、CechComma・relativeCechDiagram は ∞ 層（HTT 6.2.2.6 への通常圏の入力、InfinityCategories/Sheaves/）用で、幹 C「∞ 層」に入れてもよい。重複の疑い：Čech 複体の作り方が三通り（fullCechComplex＝有限交叉図式の全タプル版、Cech.augmentedCochain＝増大余単体対象の交代余面、Cosimplicial.cochainDifferential＝余単体的環の交代余面）。FullCechCochains と FullRingCechCochains は係数が加群か環かの違いだけ。cechRefinementCone は一般の ℕ 次数複体の写像錐の添字付け直しで Čech 固有ではない（cechIntegerLiftTotalFunctor も Mathlib の totalFunctor の別名）。

## A 可換代数と数論幾何/δ 環（d08）

46 件中 28 件が δ 除算 A{a/d}（prismatic envelope の構成部品、Delta/Division/）で、δ 環の基礎（18 件）とは別の塊。幹を「δ 環（基礎）」と「δ 除算と prismatic envelope」に分けるか、後者を「プリズム」の envelope の小概念に寄せる余地がある。δ 除算の環が段階ごとに多数ある：DeltaAdjoinDivision（raw）→ DeltaDivisionTorsionQuotient（ねじれ除去）→ ClassicalDeltaDivisionCompletion（古典完備化）／DerivedDeltaDivisionCompletion（導来完備化の H⁰、derivedDeltaDivisionCommRing の対象）／Semiperfectoid.PCompletedDeltaDivision（完全化）。古典完備化と導来完備化の二本があり、どちらが主経路かは確認が要る（docstring が「旧ねじれ除去」「候補の環構造」と書いており、古い経路が残っている疑い）。deltaDivisionIteratedRelation と deltaDivisionEvaluationRelation はどちらも深さ n の関係式で、定義の仕方が違う同じ元の疑い。Semiperfectoid.* の 3 件は幹「パーフェクトイド」（perfect prism）に入れてもよい。Prismatic.completedFreeDeltaStructure は envelope の始域で「プリズム」寄り。primeDividedPowerIdeal は「分冪包絡とクリスタリン」寄り（Delta/DividedPower/ の下）。

## A 可換代数と数論幾何/ほとんど数学とねじれ（d09）

幹の名前は二つの別の概念をまとめている：almost 数学（Almost.*、BS §10）とイデアルの冪ねじれ（IsPowTorsion は正規化長さ・局所コホモロジー側で使う、idealPowerTorsionFunctor は Γ_I で局所コホモロジーの零次）。後者は「台つきの加群と Tor」か局所コホモロジー寄り。perfectoidIdeal（110 宣言）は R → (R/g)_perfd の核 (g)_perfd で、定義の中身は perfectoid 化なのでパーフェクトイドへ移したが、使い道は almost 数学の基準イデアル J_perfd（BS §10.1、Definition 10.1 の零化条件）なので、ここに小概念「perfectoid イデアル」として残す判断もありうる（名前空間は BhattScholze.Almost、ファイルは BhattScholze/PerfectoidIdeal/）。DVertex は導来 ∞ 圏の頂点（(derivedInfinityCategory R) _⦋0⦌）の略記で、almost の概念ではない（完備導来テンソルの模型比較の添字、BS Lemma 10.3〜Proposition 10.4）。Almost.IsAlmostZero は I ≤ Ann M で、Mathlib の Module.IsTorsionBySet の言い換え；IsPowTorsion も IsTorsionBySet を J^n に適用したもの（どちらも言い換えの候補）。

## A 可換代数と数論幾何/スキーム（d10）

今回の 44 定義のうち 19 は別の幹へ：strict transform・中心（centerComplement, IsUAdmissibleCenter, determinantalCenter, HasFlatPurePullbacks）・チャート分数・Proj の次数一表示と Laurent チャートは blowup と射影スキーム、v 被覆（IsSchemeVCover, IsAffineVCover）と開被覆の Čech 前層は Čech 複体と被覆、Frobenius 反復系は Frobenius の順極限。残りの中心は「有限表示模型による近似（極限論法）」で、幹の名前「スキーム」より「有限表示への近似と降下」が実体に近い。重複の疑い：AlgebraicGeometry.IsAffineVCover と BhattScholze.Perfectoidization.Arc.IsAffineVCover（ArcValuationProduct.lean、同じ BS17 Definition 2.1）。「平坦化の加群論的入力」はスキームでなく可換代数（Raynaud–Gruson の入力）で、blowup による平坦化とまとめる余地あり。模型の圏は三種（FinitePresentation・Integral・CoefficientVCover）が同じ型の構成で並ぶ。

## A 可換代数と数論幾何/パーフェクトイド（d11）

PerfectoidizationInterface.completionRing は導来 p 完備化の H⁰ 環で、パーフェクトイドでなく導来完備化（ファイルも HomologicalAlgebra/DerivedCompletion）。「p 冪根つきの多項式環と根の添加」は幹の 根の添加（André）・根の塔 と境界が近い（PowerRootPolynomial は Semiperfectoid/Quasiregular/RootFamilies、algebraicStepIdeal・polyRootIdeal は Perfectoidization/Construction/RootAdjunction）。パーフェクトイド化の「選ばれた対象」が三つある：Perfectoidization（有限代数）、Semiperfectoid.QuotientPerfectoidization（全射商）、Section2.MixedPerfectoid（前者の特殊化）。PerfectoidizationInterfaceE3 は存在を公理にしない界面の型（BS §8 の結果を欄として受け取る）。

## A 可換代数と数論幾何/プリズム（d12）

幹の「プリズム」は実際には (a) プリズムそのもの（Prism/Basic）と (b) プリズマティックコホモロジー（サイト・包絡・Čech–Alexander・Hodge–Tate 比較、71 定義中 約 55）に分かれる。(b) を別の幹「プリズマティックコホモロジーと Hodge–Tate 比較」に分ける案あり。HTComparisonTotal.* は内容が一般のホモロジー代数（積全複体、半自由分解、有限列に沿う主元完備化の反復）で、プリズムに固有でない：finiteCompletionFunctor・finiteDerivedCompletionFunctor・finiteCompletionUnit は導来完備化へ、total は既存の cochainProductTotalizationFunctor の abbrev。wittPdStructure・residuePdStructure（分冪構造）と wittBigPdModel（分冪 Čech 模型）は分冪包絡とクリスタリンへ。同じ環の別名：polyCompletion P r = affineAlgebra P r = prismPolynomialCompletion P (Fin r)（三つの abbrev）。同じ模型の読み替えが多い：reducedModel → affineBaseModules → affineBaseComplex / affineHTComplex / affineHTTotalComplex / affineBaseSingleRows。hodgeTateCohomology' 上の Module の local instance が二つ（HodgeTateCompletedMap.lean と HodgeTateOneDerivative.lean、どちらも htModule）。affineHTCoefficientReduced は affineHTCoefficientReducedAny の生成元を保つ場合。

## A 可換代数と数論幾何/交点重複度と χ（d13）

IsSystemOfParameters は χ そのものでなく局所環の一般概念（CommutativeAlgebra/SystemOfParameters）。幹を「交点重複度と χ」に置くなら入力として残せるが、環と加群（その他）に置いてもよい。

## A 可換代数と数論幾何/付値と区間（d14）

ValuationProbeIndex は arc 被覆の Čech 完全性を絶対整閉付値環へ帰着する証明の添字（Perfectoidization/Arc/Valuations/ArcValuationProduct.lean）。同じファイルに Arc.IsAffineVCover があり、AlgebraicGeometry.IsAffineVCover（d10）と重複の疑い。

## A 可換代数と数論幾何/分冪包絡とクリスタリン（d15）

crystallineBasePrism（BS 著者版 Example 3.3 の結晶プリズム）と台環 crystallineBase = ULift ℤ_p はプリズムへ（d12 の cartierBase・wittCrystallinePrism と同じ小概念）。逆に d12 から wittPdStructure・residuePdStructure・wittBigPdModel がこちらへ来る。分冪 Čech 模型は未完備（pdRaw, pdRawModel）→ p 完備（pdTerm, pdModel, pdRings）→ δ 側（pdDeltaRings, crystallineExtraRaw）の三層で、同じ模型の台環の読み替えが並ぶ。分冪 de Rham は未完備の列が二つ（pdRawForms と pdUncompletedColumn：後者は HodgeTate/Comparison/Witt にあり「標数を仮定せず作った」版）で重複の疑い。Prismatic.Poly は多項式代数の小圏（CechAlexander/Comparison/PolynomialCategory）で、クリスタリンに固有でなくプリズム側でも使う（bigResidue）。代数構造の abbrev（rankOneDP*Algebra, principalDPQuotientAlgebra）は instance の足場に近い。

## A 可換代数と数論幾何/台つきの加群と Tor（d16）

台の定式化が二通りある：閉集合 Z による台（finiteModuleSupportedOn、d18 の perfectHomotopySupportedOn）と、スカラー列の冪零による台（scalarSupported、d18 の SupportedPerfectHomotopy）。scalarSupported は一般の線形圏の ObjectProperty（CategoryTheory/ScalarSupport）で、加群に限らない。SupportedFGModuleOn は G₀ の入力（KTheory/G0/Basic）で、完全複体と K₀ の G0WithSupport と一体。

## A 可換代数と数論幾何/完備平坦と整閉（環の性質）（d17）

GenericEtale.awayAlgebra（局所化 A[1/g] → D[1/g] の代数構造）と adicQuotientAlgebra（R/I → S/IS の代数構造）は環の性質でなく instance の足場で、環と加群（その他）へ。幹の名前は三つの無関係な性質（完全平坦・絶対整閉・普遍同相）の寄せ集めで、「環と射の性質」としてまとめるのが実体。

## A 可換代数と数論幾何/完全複体と K₀（d18）

scalarPerfectHomotopyExtension は dg 加群の Perf のホモトピー圏（PerfectDGHomotopyCategoryOver）の間のスカラー拡大で、名前の PerfectHomotopy に当たっただけ（B の 導来圏と Perf（dg 加群）、または 係数の取り替え）。台つき完全複体が二系統：SupportedPerfectHomotopy（スカラー列 z、scalarSupported による）と SupportedPerfectHomotopyOn（閉集合 Z、K0WithSupport はこちら）。G0WithSupport は d16 の SupportedFGModuleOn・finiteModuleSupportedOn と一体で、G₀ の側にまとめるのがよい。

## A 可換代数と数論幾何/導来完備化（d19）

「有界上導来圏の導来テンソルと底変換」（14 定義、boundedAboveDerived*）は完備化でなく通常の環の導来圏 D⁻(Mod R) の一般論で、幹に合う場所がない（B は dg 加群の導来圏）。別の幹「加群の導来圏（導来テンソル・底変換）」を立てるか、幹の名前を「導来圏と導来完備化（通常の環）」にする案。ConcreteDerivedCategory は Mathlib の DerivedCategory (ModuleCat R) の abbrev、moduleObjectFunctor は singleFunctor 0 の別名で、boundedAboveDerivedSingleFunctor と役割が重なる。Koszul 還元が二つ：derivedScalarConeFunctor（D 全体）と boundedAboveDerivedScalarCone（D⁻）。H⁰ の環は Principal → Iterated → Pair → PD と積み上がり、PDCompletionH0 p d = PairCompletionH0 (p) d の abbrev、pdCompletionCommRing・pdCompletionUnit も pair 版の言い換え。CompletedRing は principalCompletionRingCat の p での abbrev。d12 から HTComparisonTotal.finiteCompletionFunctor・finiteDerivedCompletionFunctor・finiteCompletionUnit（有限列に沿う反復）、d11 から PerfectoidizationInterface.completionRing がこちらへ来る。

## A 可換代数と数論幾何/根の塔（d20）

towerLengthFun（λ_∞、論文 (2.3)）・towerLengthOn（λ_D）・RootTowerLength.completedNormalizedLength は塔の上の正規化長さで、幹の 正規化長さ へ（NormalizedLength 構造の実例。ファイルも LengthAlgebra/RootTowerLength）。towerMap（代数射）と towerMapRingHom（環準同型）は同じ遷移の二つの形。完備化した塔 CompletedTower と d11 の Section2.MixedPerfectoid（C_D = (R∞ ⊗ D)_perfd）はここに来ていない。

## A 可換代数と数論幾何/根の添加（André）（d21）

全 56 件に docstring があり、本体は開かず docstring と signature で分けた。幹の名前は「根の添加（André）」だが、中身の大半は BS Remark 7.15 の prismatic envelope（δ 除算包）の平坦性計算で、通常の根添加環は一部。重複の疑い：源対象の三系統が同じ形（DeltaRootSourceIteratedPDCompletion／MonicPrismaticSourceIteratedPDCompletion／PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional はどれも (Cd).obj ((Cp).obj X₀)；DeltaRootSourceCoefficientObject／MonicPrismaticSourceCoefficientObject／…_of_unconditional；DeltaRootSourceQuotientDerived／MonicPrismaticSourceQuotientDerived；deltaRootSourceQuotientResidueMap／monicPrismaticSourceQuotientResidueMap は本体が同文）。p 乗根の特別な場合（DeltaRoot…）とモニック多項式の一般の場合（MonicPrismatic…）、仮定を外した版（_of_unconditional）の並行。monicPowerFamilyRelationIdeal（冪根）と polynomialFamilyRelationIdeal（一般多項式）も特別・一般の関係。divisionPrism は docstring に「別経路の一段候補」とある。perfectPrismVarpi 系は完全 prism 一般の事実で「パーフェクトイド」か「プリズム」に移してもよい。PowerRootCoefficientPDEnvelope は「分冪包絡とクリスタリン」に近い。BoundedPrismInput は「プリズム」に近い。monicRelation・polynomialFamilyRelationIdeal は名前に monic とあるが定義にモニック性はない（docstring に明記）。

## A 可換代数と数論幾何/正規化長さ（d22）

6 件とも docstring で内容が言える。d23 の ordinaryLengthOnIdeal（通常の長さを NormalizedLength として与える）はこの概念に属する。

## A 可換代数と数論幾何/漸近的なランク（d23）

docstring のない paperSequenceFunctor・paperBaseChangeEulerK0 は本体とファイル冒頭を読んだ。幹の名前「漸近的なランク」はランク商の側だけを指すが、加群列の長さの Serre 商（LengthSerreQuotient など）も入っている。ランク商が二つの順序で作られている：Kar(K^b/N)（CompletedSequenceRankQuotient）と論文の順序 Kar(Kar(K^b)/N)（PaperRankQuotient）で、同値 paperRankEquivalence でつないでいる。台つき部分圏も supportedSequence／supportedCompletedRankQuotient／paperSupportedRank の三段がある。ordinaryLengthOnIdeal は「正規化長さ」へ。

## B 複体と dg 圏/dg 商と cell 分解（d24）

docstring のない 15 件は本体を読んだ。重複の疑い（並行する構成）：DGQuotient の path 複体と DGCellAttachment.Family の語の複体は同じ形（term／internalHom／ι と inclusion／prependMap／internalComposition／erasure と replacement／quotientHom と attachedHom／lengthComplex と lengthHom）。dg 商は「次数 −1 の cell を恒等射を境界として貼る」場合に当たるので、cell の貼り付けの特別な場合として書ける見込み。resolvedDGQuotientNerve・…Functor・…Projection・…ThickFlatKernel は cell 分解した dg 圏の dg 商の神経と thick 閉包の核で、∞ 圏の Verdier 列の部品（ファイル冒頭に「D-16 の Sp 向け kernel 欄」）なので「Verdier 列」へ。dg 商の係数変更 3 件は「係数の取り替え」に置いてもよい。d25 の DGCategoryCycleCover.Source は cell 分解の初段（stage 0）でこの概念に属する。

## B 複体と dg 圏/dg 圏と dg 関手（d25）

docstring のない 7 件は本体を読んだ。DGCategory・DGFunctor・DGTensorCategory・ClosedCategory は Mathlib の EnrichedCategory／EnrichedFunctor／TransportEnrichment／ForgetEnrichment の abbrev。DGCategoryCycleCover.Source は Hom の cycle cover を辺とする自由 dg 圏で、cell 分解の初段（DGCategoryCellResolution.initial が使う）なので「dg 商と cell 分解」へ。自由 dg 圏（FreeDGCategory）の path のテンソルの直和は、d24 の dg 商の path 複体・cell の貼り付けの語の複体と同じ形の三つ目の構成。DGCategoryPresentationCode は「サイズの条件」に近い（表示の符号で小ささを示す足場）。

## B 複体と dg 圏/係数の取り替え（d26）

docstring のない DGRestriction・restrictDGFunctor は本体を読んだ。全件が DifferentialGraded.ScalarExtension にあり内容も一致。d24 の dg 商の係数変更（quotientScalarTriaFunctor など）はこの概念の続き。

## B 複体と dg 圏/単体的鎖とシャッフル（d27）

docstring のない simplicialRingCoefficient は本体を読んだ（ULift ℤ の abbrev で、宣言 100 件がこれを主張に含むが、中身は「単体環の正規化 cochain を dg 複体へ移す」作業の係数型。数学の概念ではない）。重複の疑い：同じ内容が二系統ある。(1) SimplicialChains（Berger–Fresse、係数 A、SSet.{0}）：chains／cochains／AlexanderWhitney.component／Shuffle.value と ShufflePath。(2) Kerodon…DifferentialGradedCategories（KST Appendix A、ℤ 係数、任意の宇宙）：linearizedSpace と normalizedMooreComplex／normalizedAlexanderWhitney／ShuffleIndex。シャッフルの添字型も ShufflePath（格子経路）と ShuffleIndex（Fin n の p 元部分集合）の二つ。integerTensor・integerTensorBifunctor・chainIntegerTensor は Mathlib のモノイダル構造の明示的な写し（宇宙を独立にするため）。(2) の名前空間は Kerodon の「dg 圏」の節だが中身は KST Appendix A の群ホモロジーの鎖の議論で、置き場所と内容が合っていない。linearizedSimplicialWeight（HA 1.2.4、集合値の単体的重みの線形化）は重みつき余極限の文脈で、ここでは線形化に入れた。groupLinearizedMap・LinearizedCylinderEquivariant は KST の pro 切除（GL の群ホモロジー）で使う。

## C 単体集合と ∞ 圏/necklace と立方体（組合せ）（d28）

docstring のない 7 件と、docstring だけでは分からない数件（FiniteSpanIndex・HornBoundaryOver.horn・SimplexHABeadWord・cubeJoinNormalFormEval・sigma・simplicialSum）はファイル冒頭と本体を読んだ。この概念に属さないものが 13 件：UniverseLiftFillers.obj/map（uliftFunctor の abbrev）、VertexTuples.obj/vertices（n ↦ A^{n+1} の単体集合と定数単体集合）、interval・one（Δ¹ と端点への定数写像）、sigma（標準単体の退化）、standardSimplexVertex、simplicialSum（余積、Segal の telescope 用）、HornBoundaryOver.horn は「単体集合（基本）」へ。BoundaryFillers（全ての境界が埋まる＝自明ファイブレーション型の条件）は「Kan 複体とホモトピー群」へ。hornObj（coherent 神経へのホーンから対象を取り出す、HTT 1.1.5.10）は「単体的圏と coherent 神経」へ。FiniteSpanIndex（三点の半順序 span の添字）は「ねじれ矢と余スパン」としたが「組合せと順序」でもよい。中断した経路の部品：UniverseLiftFillers・VertexTuples・ParameterCube はファイル冒頭に「任意モデル源への一般化（中断、計画書 §396）」「stage 4 の完成部分からの利用はない」とある。重複の疑い：立方体が三通り（CubeVertex = Fin n → Bool、cube T = nerve (Set T)、ParameterCube.obj = (Δ¹)^n）。coherent resolution（Kerodon 4.6.7）と cube・pathThrough（HTT 1.1.5.10）は coherent 神経の Hom の計算の部品で、「単体的圏と coherent 神経」または「写像空間」に置く考えもある。necklaceLambdaCell は KST の S 構成（cubical Λ の Hom への Serre 鎖射）で、necklace から dg 側への橋。necklaceBead は NecklaceShape.single の宇宙つきの言い換え。

## C 単体集合と ∞ 圏/∞ 層（d29）

全 20 定義が Sheaves の下にあり、MOVE はなし。層は Čech 層（hypersheaf ではない）で、site は小さい通常の圏に限る。Sheafification は存在を仮定した Prop（IsReflectiveSubcategory）で、存在は別の定理 sheafification_exists。siteLiftPresheaf は宇宙の持ち上げだけの定義で、数学の内容は重み付き切断の係数移送。discretePresheafInclusion は部分型（射と評価仕様の組）で discretePresheaf と内容が重なる。

## C 単体集合と ∞ 圏/ねじれ矢と余スパン（d30）

幹の名前は「ねじれ矢と余スパン」だが、今回の 23 定義に余スパン（cospan）の定義は一つもない（全部 edgewise subdivision とねじれ矢）。RightFibrationObject・RightFibrationInfinity は Kerodon の節の場所でここに入っていただけで、中身は固定した底の上の右ファイブレーションの単体的圏と coherent 神経（LeftFibrationObject・LeftFibrationInfinity の右版）→ ファイブレーションへ。TwistedArrow は edgewiseSubdivision の abbrev（同じもの）。edgewiseRightExtensionDomain と twistedArrowExtensionDomain は別の延長領域（前者は右射影の持ち上げ、後者は i 番目のホーン）。

## C 単体集合と ∞ 圏/サイズの条件（d31）

4 定義とも Kerodon §4.7 相当のディレクトリにあり、docstring に文献の節番号はない。HasEssentiallySmallFibers（同値まで）と HasSmallSimplexFibers（集合として）は別の条件。IsKappaSmall の使い道は κ-filtered の試験図式なので、「表現可能 ∞ 圏とフィルター」と接している。

## C 単体集合と ∞ 圏/ファイブレーションと straightening（d32）

MOVE 12 件：(1) TwoSidedElements.Hom・map、TwoSidedGrothendieck.contravariantTotal・right・baseMap、Hammock.TwoSidedDiagram.FixedVertices.leftSpace・rightSpace、TwoSidedDiagram.diagonalTotalNerve の 8 件は Dwyer–Kan の二方向 bar・hammock（DK §9〜10）で、ファイブレーションではない（docstring なし、本体とファイルの冒頭で確認）→ 局所化（Dwyer–Kan）。(2) coherentNerveMap・coherentSimplexMaximalization・SimplicialPairObject は単体的圏と coherent 神経の一般論。(3) coyonedaInfinityMap はねじれ矢から得た Hom 二変数関手の curry（Yoneda）で、写像空間へ（幹に Yoneda の概念がないので、空間・Cat∞・前層・Ind か、ねじれ矢でもよい）。名前で誤って入りそうなもの：cartesianEdgePair は cartesian 辺ではなく直積の辺（（補助）関手空間へ）。重複の疑い：universalScaffold（左）と cocartesianUniversalScaffold は docstring がほぼ同文の左版と cocartesian 版；leftStrictTransportEvaluate と cocartesianStrictTransportEvaluate も同じ対；cocartesianTwoSimplexLocalSource/Comparison と cocartesianScaffoldLocalSource/Comparison は docstring が同文（二単体版と scaffold 版）；leftUnstraighteningMap と smallLeftUnstraighteningMap、leftUnstraighteningFiberIso と smallLeftUnstraighteningFiberIso は大小の模型の対。（補助）cocartesian 分類の Hom 比較 が今回も 43 件と最大で、cocartesianBaseChange…Hom…（Span・Triangle・Path・Restricted・Associativity）の族は一つの証明（底変換と分類の両立の Hom 上の自然性）の部品。relativeArrowCollageProjection は「射の coherent な分類の実現の候補」とあり、復元の経路の部品（使い切られているかは未確認）。（補助）関手空間 の定義（functorFamilyPrism・functorEdgePrism・functorIsoValue・doubleFunctorEvaluation など）は内容としては「関手単体集合と同値」に属する一般の道具。

## C 単体集合と ∞ 圏/冪等完備とモナド（d33）

幹の名前「冪等完備とモナド」は二つの別の概念の合併：(a) 冪等と retract（Kerodon の Retracts and Idempotents、18+2 定義）、(b) HA §4.7 のモナドのための自由随伴 Adj（Riehl–Verity、39 定義）。今回の定義にモナドそのもの（代数、Eilenberg–Moore、Barr–Beck）はなく、(b) は全部 Adj の組合せ論。幹を「冪等完備」と「自由随伴 Adj（モナドの入力）」に分けるのがよい。未完の印：walkingAdjunctionOrdinalWidth の docstring に「文字列の幅との全比較は未完」、WalkingAdjunctionAtomicCell.NativeFillable に「原典の文字列の条件との全比較は未完」（Riehl–Verity §4 の経路が途中）。（補助）有限順序の単調射（ordinalAppend・ordinalGlue・ordinalIntervalMap など）は内容としては「Z 圏論一般/組合せと順序」でもよい。retract 関係の冪等完備化 Idem(C) は Kerodon の節の docstring に番号がない。

## C 単体集合と ∞ 圏/単体的圏と coherent 神経（d34）

coherentSpaceSectionsObject は空間値図式の切断の Kan 対象（極限頂点の候補）で、極限と余極限の「空間値の図式の極限と切断空間」の内容。spaceInfinityObject は 𝒮 の頂点の Kan 複体の読み出しで coherentNerveObject の 𝒮 への特殊化（言い換え）。coherentTransformationFamilyDiagram は leftUnstraightening の変換空間の図式で、空間値関手（または straightening）の側。pathAvoids・pathThrough による Path の境界の被覆は、局所化（d36）にあった pathCubeBoundaryFace と pathHollowFace が同じ内容を別の添字で持つ（重複の疑い）。

## C 単体集合と ∞ 圏/基点付き対象（d35）

場所は Spectra/Pointed と InfinityCategories/HTT/PointedSimplicialSets の二か所に分かれているが内容は一続き。sphereSequence は球面の対称列で対称列の概念。sphere 1 = circle、spherePower（TensorPowers.power circle n）と sphere n は別の球面の模型（比較の有無は未確認）。sphereZero（一般の PointedObject）と smash の単位。

## C 単体集合と ∞ 圏/局所化（Dwyer–Kan）（d36）

場所が Project/HomotopyDiagramComparison の定義の大半は局所化ではない。(1) specifiedCocone…・partialColimit…・transportedCoconeVertex の 20 余りは「形状の押し出しに沿って部分余極限の余錐を貼る」（coherent 図式のセル付加）一つの証明の部品で、極限と余極限へ。延長空間・円柱・四面体の族など足場が多い。(2) finalHorn…・pathCubeBoundaryFace・EnrichedAdjunctionHomComposition は HTT 5.2.4.6（豊穣随伴から coherent 神経の随伴）の外側ホーン充填の部品で、単体的圏と coherent 神経へ（随伴の側でもよい）。(3) nonemptyFiniteSSetProduct・finiteKanProductObject は sifted 余極限と有限積の交換のための有限積。重複の疑い：prismVertexEvaluation（ここ）と familyAtVertex（極限と余極限、d37）は同じ定義 lift (𝟙) (const v) ≫ F。pathCubeBoundaryFace は pathHollowFace（d34）と同じ被覆。HammockObjects・LocalizationObjects・KanLocalizationObjects・KanFreeHammockObjects は対象の型の別名（豊穣構造を載せる札）。DiscreteEnrichment.enrichedCategory は一般の離散単体的豊穣化で単体的圏の側。modelBifibrantSourceRoofDegreeObject と modelBifibrantSourceRoofProjection は別ファイルに同文の docstring（分割の跡）。commaTargetFiberArrow は comma の fiber の点から辺を読むもので随伴の単位の比較用（行き先は推定）。

## C 単体集合と ∞ 圏/極限と余極限（d37）

controlledTriangle…（FamilySpace・LongHomSpace・LongHomValue・CompositeFamily）、composableHomHornMap、innerTriangleExtensionUncurry、triangleFullPath、triangleZeroLabel は「Ind-S (9)」と呼ぶ一つの証明（𝒮 の中の合成三角形の空間と全長 Hom の空間の比較）の足場で、極限そのものではなく写像空間・合成の内容。familyAtVertex は局所化（d36）にあった prismVertexEvaluation と同じ定義（重複）。PreservesZeroVertices は零対象を保つ関手の条件で安定 ∞ 圏（完全関手）の側。nerveAsSmallIso は神経の宇宙の持ち上げ。catPullbackReplacement… は Cat∞ の引き戻しで、空間・Cat∞ の側に置く手もある。vertexDiscreteι は一般の単体集合の構成（頂点の離散化）で、単体集合（基本）に置く手もある。

## D 安定 ∞ 圏と導来 ∞ 圏/Verdier 列（d38）

DGVerdierDiagramVertexCone・dgVerdierDiagramEdgeHorn・dgVerdierDiagramTriangleHorn は dg の Verdier 商の分母の圏がフィルター的であることを示す途中の部品（docstring に「最後の面の充填可能性は主張しない」「高次整合性はまだ構造に含めない」とあり、中断した経路の可能性）。RelativeInvariant.lean の冒頭に「分割で生成：docstring を書き直すこと」。

## D 安定 ∞ 圏と導来 ∞ 圏/dg 代数（一対象 dg 圏）（d39）

二つだけの概念。内容は「B 複体と dg 圏/dg 圏と dg 関手」の例（一対象 dg 圏）で、幹として独立させず統合してよい。導来 ∞ 圏 D(A) と ⊗_A B の入力に使う。

## E モデル圏/Quillen 関手と生成（d40）

ArrowFactorization は一般の圏の射の因子分解のデータ（モデル構造なし）で、Mathlib の MapFactorizationData と役割が重なる（言い換えの疑い）。ファイルの冒頭に「任意モデル源の厳密化から独立」とあり K 理論の一般化（中断）の跡。Smith.arrowProperty は MorphismProperty を Arrow の ObjectProperty と見るだけの言い換え。CofibrantlyGenerated の Basic.lean の冒頭に「分割で生成：docstring を書き直すこと」。

## E モデル圏/Reedy（d41）

docstring のない定義が大半（38 中 34）。r5・r6 は Reedy モデル構造の因子分解・持ち上げを次数の帰納で作る一つの構成の部品。CofibrantResolution・CofibrantResolutionFamily は「E モデル圏/ホモトピー関数複体と分解」の frame と同じ内容で、そちらに置く手もある（ファイルも HomotopyFunctionComplex/Reedy）。Elements.lean の冒頭に「stage 4 の完成部分からの利用はない」「任意モデル源への一般化 中断 2026-10-17」とあり、elementsReedy は中断した経路の部品。Mathlib に AlgebraicTopology/Reedy/Basic（ReedyStructure）があり、それを土台にしている。simplexInverse は epimorphisms SimplexCategory の別名。

## E モデル圏/単体的モデルと anodyne（d42）

（1）このキーの 60 定義のうち 37 は、ファイル冒頭に「中断した任意モデル源への一般化（計画書 §396、分類 B）」とある止めた経路の部品（HomotopicalAlgebra/Rectification/Simplicial/ の Nerve*・KanComparison*・*Choices・WordPresentationDiagram・(Word)RetractChainFamily・ParameterCategory/ParameterComposition・NormalizedHornTargetComparison・DegenerateHornInput・SmallSubdiagramObstruction・StrictValueObstruction）。d44「語による分解（小対象の議論）」の中身が同じ経路（RetractWords・WordSegment・NerveCoherentFamily・KanComparisonTriangle）なので、まとめて d44 の概念へ MOVE とした。d44 側の小概念との対応：Nerve*（LowerSystem・System・values・evaluate・restriction・valueMap・ofNatTrans・expand・NerveCylinderBoundary.boundary）→「（補助）止めた経路：nerve の単体上の整合的な族」；KanComparisonSquare/Tetrahedron.Filler・ComparisonTriangleChoices.obj・ComparisonCoherenceRestriction.triangle・NormalizedHornTargetComparison.*・DegenerateHornInput.boundary・KanTriangleFamily.parameter・RestrictionDescentChoices.obj・ParameterChoiceDiagram.diagram →「（補助）止めた経路：Kan 比較の三角形」（四面体・正方形・horn の充填の選択も含めて）；WordPresentationDiagram.smallHom・WordRetractChainFamily.Chain(.append)・RetractChainFamily.Chain(.append)・ParameterCategory.Object・ParameterComposition.const/comp → 語で表示した圏／語の区間；SmallSubdiagramObstruction.Index・StrictValueObstruction.Base/value は厳密化の障害の反例（新しい小概念「（補助）止めた経路：厳密化の障害の反例」が要る）。（2）幹の名前について：d44 は小対象の議論ではない（小対象の議論による分解は AnodyneKanReplacement・MonoLocalizedFactorization でこちらにある）。d44 を「止めた経路：任意モデル源への一般化」と改名するのがよい。（3）重複：WordRetractChainFamily.Chain と RetractChainFamily.Chain は区間の型（WordSegment.obj と interval）だけが違う同じ帰納型で、append も同文。NerveLowerExtension.LowerSystem と NerveDiagramExtension.LowerSystem は後者の特別な場合。HomotopyBinarySquare.interval・WordSegment.interval・BoundaryOneCotensor.vertex は Δ¹・Δ⁰ の言い換え。（4）bar 構成（BarConstruction.*）はホモトピー余極限の模型で、d43 の「ホモトピー余極限」に寄せる案もある。SimplexIndexFinite.reedy は要素の圏の Reedy 構造の言い換えなので Reedy へ、SimplicialModelInputs.simplicialLevelModelCategory は対称スペクトルの level モデル構造なので対称スペクトルへ MOVE。

## E モデル圏/図式と二重単体集合のモデル構造（d43）

幹の名前は「図式のモデル構造とホモトピー（余）極限・重みつき実現」が中身に合う。二重単体集合は対角関手 BisimplicialModel.diagonal の 1 件だけ（41 宣言）で、d42 の BarConstruction.functor（rows ⋙ diagonal）の部品。SmallHomFrameWeights.functor は FrameWeightRealization.functor を SmallHomModel の同値で運んだ言い換えに近い。ContinuousLifts.Partial は順序つき図式に沿う超限的な持ち上げの足場（どの定理のためかは本体から確認していない）。

## E モデル圏/語による分解（小対象の議論）（d44）

幹の名前が中身と合わない：ここにあるのは小対象の議論ではなく、止めた経路「任意モデル源への一般化」（計画書 §396、各ファイル冒頭に「中断」と明記、「stage 4 の完成部分からの利用はない」）の部品。「止めた経路：任意モデル源への一般化（語による表示と nerve 上の整合的な族）」と改名するのがよい。d42 に入っていた同じ経路の 37 定義もここへ MOVE とした（d42 の notes に対応表）。その受け皿として小概念「（補助）止めた経路：厳密化の障害の反例」（SmallSubdiagramObstruction・StrictValueObstruction）が別に要る。MOVE：RelativeChoiceSpace.*（obj・family・name・pointUnitIso・FixedBoundaryHomotopy、境界を固定した延長の空間＝内部 Hom の制限のファイバー、ファイルは中断の印なしの一般的な道具）は d42 へ（そこで新しい小概念「境界を固定した延長の空間」）；NerveSimplexEndpoint.*（Index＝nerve の要素の圏の反対、dimension、endpoint＝最後の頂点）は神経へ。重複：AmbientWords と RetractWords は同じ作りで後者が small 頂点と分裂を足したもの（Obj・quotient・Vertex・Rel が二組）。WordSegment.interval は interval の言い換え、RelativeChoiceSpace.pointUnitIso は Δ⁰ ≅ 𝟙 の言い換え。

## F オペラドと E∞/Barratt–Eccles と全射オペラド（d45）

（1）114 定義のうち 38 は BE オペラドそのものではなく、BE 代数（(operad A).Algebra）の圏の上の構成で、名前空間 EInfinity.BarrattEccles にあるだけ：cofibrant 代数と DK 局所化・相対圏（CofibrantAlgebra・cofibrantAlgebra*・algebraRelativeCategory・allAlgebraRelativeCategory・cAlgVertex）、hammock（algebraHammockLengthStage・algebraReducedHammock・algebraSpecialHammock・cofibrantHammockVertex・cofibrantSourceFrameRoofMap）、frame と定値図式・試験始域（rightFrameFamily・rightFrameDiagram・constantDiagram*・framedLimitProbe*・freeProbe*・Diagram.forget・carrier 版 2 件）、加群（strictRawModule*・moduleTotalInfinity・assocForget）、離散代数（discreteAlgebraFunctor）、HA 3.2.4.7 の二色の置換（twoColorPermutationHom）。全部「E∞ 代数の圏（CAlg と加群）」へ MOVE とした。そちらの小概念としては「cofibrant 代数と DK 局所化」「hammock と写像空間」「frame・定値図式の置換・試験始域」「BE 代数上の加群（strictRawModule）」に分かれる。carrier 版（CarrierDiagram.constantDiagramSourceHom・carrierFramedLimitProbeFunctor）は複体の射影モデルの上の同じ構成で、代数版と対になった重複。（2）SchurWordIndex は BE の Schur 表示の語の基底（セル代数の次数つきの台）で、d46 の「セル代数の次数つき自由表示」へ MOVE。（3）新しい小概念は「（補助）shuffle 合成の微分両立の証明」1 個（MixedCorner・HorizontalCorner・horizontal/verticalInsertionEquiv・ShufflePath.swapSteps・degreeTransport）。（4）重複に見える組：SimplexCuts.Nondegenerate と Surjection.Nondegenerate（別の条件、名前だけ同じ）；IntervalCuts（Δ¹ の場合）と SimplexCuts（一般の S）は同じ切断公式の二つの版で、simplexDegree/tupleDegree/tensorVector と vectorDegree/label/colorPositions が対応；SimplexCuts.previousVertex は Surjection.previousOccurrences の最大。（5）StoppedRoutes.ISW2Tot の 6 件は既存の止めた経路の小概念へ。

## F オペラドと E∞/dg オペラドと代数（d46）

43 定義とも dg オペラドと代数に属し、MOVE はない。セル代数の 4 件（EInfinity.Operad.CellsAt・cellDegree・cellStageGeneratorSpheres・eraseAlgebra、場所は EInfinity/BarrattEccles/Theory/）は BE に固有ではなく一般のオペラド P の代数の話（BM 命題 4.1、cofibrant 代数の台の K 平坦性のため）なのでここに置いた；d45 の SchurWordIndex もこの小概念へ。有限族のテンソル（tensorFamily など 12 件）は対称モノイダル圏の一般論で、複体に固有ではない（「Z 圏論一般/モノイダル圏」か「G スペクトル/対称列」の道具に上げる候補）。tensorPowerEquivMap は既存の bijectionFunctor の評価の言い換え、Operad.arityBijectionMap も対称列の map の言い換え。合成は composeFirstInputs（再帰）→ composition（k=0）で、composeFirstInputInsertion・composeAheadOfInputs は arity の式を合わせるための移送つきの版。

## F オペラドと E∞/冪作用（d47）

16 定義のうち冪作用そのもの（作用素 Pⁱ など）の定義はなく、入力の準備だけ。MOVE 4 件：complexRelativeCategory・complexRelativeUp・complexRelativeDerivedSource は全複体の相対圏（射影モデルの弱同値）と既存 D(A) への比較（ComplexHammockSource 冒頭「DAG XIII §2.2 の native な降下への前段」）で導来 ∞ 圏へ；Coxeter.adjacentTransposition（49 宣言）は型 A の隣接互換（GroupTheory/Coxeter/TypeA）で、冪作用とは無関係（名前の規則の誤り）、幹に群論の置き場がないので「組合せと順序」とした。Eilenberg–MacLane 空間（gamma*・levelSpaceFunctor）は複体から基点つき単体集合・スペクトルの段を作る構成で、「G スペクトル」または「C 基点付き対象」に移す案もある。PowerOperationCyclicGroup（ULift (Multiplicative (ZMod p))）と MayCyclicGroup（BE の対称群の中の巡回置換の像）は同じ Z/p の二つの表示。May* と gamma* は docstring と signature だけで判断した。

## G スペクトル/Ω スペクトル（Bousfield–Friedlander）（d48）

今回の 111 件のうち約半分（50 件）が証明の足場。（補助）loop と随伴の比較 は 35 件で、AdjointLoopRelativeBF.*（middle・inclusion・target・fullCompatibleSpace、D3Common* の commonRefinement 系）と RawSpectrumMapping.kanAdjoint*（Traced・Boundary・Parameter の三系統）からなり、同じ比較（Kan 随伴の構造射を厳密化して loop の随伴を得る）を座標を変えて何度も組み直した跡に見える（KanAdjointBoundaryCoordinate／KanAdjointBoundaryStructureContraction と kanAdjointTraced* は別経路の部品の疑い）。幹の範囲について：点つき単体集合の一般論（PointedSmallProduct.obj、PointedKanReplacement.obj/functor、SimplicialFunctionComplex.pointedObj）は「基点付き対象」へ、厳密な豊穣自然変換を coherent 神経へ移す道具（StrictEnrichedTransformation.componentHom、EnrichedOrderedCylinder.stageInclusion、CoherentPathCoordinates.flaggedPath、d3GradedHom）は「単体的圏と coherent 神経」へ、基点なしの path 対象 KanPath.object は「Kan 複体とホモトピー群」へ MOVE とした。既存の小概念「点つき写像空間と区間族」「点つき空間の loop・path・fiber・cofiber」も中身は空間の水準で、同じく「基点付き対象」「Kan 複体とホモトピー群」の候補（pointedConnectingHom・pointedConnectingZero・SphereSimplex.equiv・SimplexCell.sphere・cellCofiber・VerticalPath.* など）。NormalizedValueCochains.complex は単体集合の正規化 cochain 複体で、K 理論側の KST.Comparison.integralHomology（正規化鎖）と対になる一般の道具。重複の疑い：rationalizationModel は tail (cotensor CirclePower.space X) そのもので、signedLoopRawComparison・signedLoopComparison・signedLoopSourceTwist の源と同じ対象に別名を付けている。KanSequence.freePath は KanSequence.mapping の特殊化（abbrev）。loop の模型が signedLoopModel・adjointLoop・tail∘cotensor・native loop の四つ並んでいる。

## G スペクトル/モノイダル圏の中の加群（一般論）（d49）

中身は対称モノイダル圏のモノイド対象上の加群（Mathlib の Mod C M）の一般論で、スペクトルに固有のものはない。幹としては「Z 圏論一般/モノイダル圏」の下に置くのが自然（使い手は対称スペクトル＝球面対称列上の加群）。Enriched.TensorCotensor は豊穣圏の tensor・cotensor の表現データ（二つのパラメーター付き随伴）で加群ではないので「豊穣圏」へ MOVE。tensorLeftObj は名前空間 MonoidalBalancedTensor にあるがファイルは FreeTensor.lean で、tensorRightObj と対。文献の記載は docstring にない。

## G スペクトル/対称スペクトル（d50）

全て対称スペクトルに属する（MOVE なし）。同じ構成が一般の対称モノイダル圏 C と対象 K（GeneralSymmetricSpectrum.*）と、点つき単体集合と円（SymmetricSpectrum.*）の二層にあり、後者は前者の特殊化か MonoidalBalancedTensor／MonoidalModuleInternalHom の直接の適用：freeAt（abbrev で一致）、pointwiseTensor（SymmetricSpectrum 側は SymmetricSequence.pointwiseTensorModule を直接呼び、General 側と並行）、cotensor／cotensorFunctor、mappingObject／pointedMappingSpace が重複の候補。SymmetricSpectrum.sphereTensor・internalHom は「モノイダル圏の中の加群」の moduleObj の言い換え。GeneralSymmetricSpectrum.level の docstring は「基点付き単体的集合」と書くが値は一般の C（docstring の古さ）。文献の記載は docstring にない（Hovey–Shipley–Smith に当たる内容だが書かれていない）。

## G スペクトル/対称列（d51）

TensorPowers.power・map・appendIso・oneIso・swapFirstIso・adjacentIso・permutationAction は対称モノイダル圏の対象の反復テンソルと対称群の作用で、対称列を使わない一般論なので「モノイダル圏」へ MOVE（TensorPowers.bijectionFunctor は対称列 Sym(X) そのものなので残した。tensorPowerSequence はその言い換え＝重複の候補）。FiniteBijection.* は添字の圏として残したが、中身は有限集合の組合せ（ファイルは CategoryTheory/Limits.lean）で「Z 圏論一般/組合せと順序」に置く整理もありうる。freeBlockQuotient と freePermutationQuotient は同じ誘導（Σ_m ×_{Σ_{m-n}} …）の二つの余等化子表示で、freeInductionDiagram の余極限と合わせて三通りの表示が並ぶ。unshiftedInternalHom と shiftedInternalHom 0、unshiftedInternalHomFunctor は同じものの対象版・関手版。SymmetricSequence.pointwiseTensorModule は加群（Mod）を返すので「モノイダル圏の中の加群」「対称スペクトル」との境界にある。文献の記載は docstring にない。

## H K 理論/K 理論の模型の比較（d52）

幹の名前は「模型の比較」だが、今回の 29 件に比較そのもの（plus 構成と S 構成の同値など）はなく、中身は KST Lemma 2.13（BĜL と群完備化）へ向けた Segal 1974 §1 の単体集合での作り直しと、plus 構成の acyclic 性のためのホモロジー。名前は「群完備化と plus 構成（Segal・KST 2.13）」の方が合う。MOVE はしなかったが、一般の単体集合の道具がかなり混じる：fatRealization・fatSkeleton・FatNormalForm・diagonalRowEvaluation・freeDegeneracies（二重単体集合、「E モデル圏/図式と二重単体集合のモデル構造」または「単体集合（基本）」の候補）、mappingCylinder・spanCylinderFunctor・homotopyPullbackObject・sliceFiberFunctor・partialSectionObject（単体集合のホモトピー（余）極限とスライス）、integralHomology・LocalCoefficientSystem（単体集合のホモロジー、「B 複体と dg 圏/単体的鎖とシャッフル」の候補）、componentSubcomplex（π₀ による部分単体集合、「Kan 複体とホモトピー群」の候補）。monoidGroupCompletionSpace・regularBar・fatRealization の docstring は「同値性・収縮・対角との比較は別途」と書いており、経路が途中の可能性。G スペクトル側の NormalizedValueCochains.complex（正規化 cochain）と integralHomology（正規化鎖）は別々に作られている。

## H K 理論/S 構成と K スペクトル（d53）

この概念に残るのは 362 件中 204 件、MOVE は 158 件。index.json の概念名「H K 理論/S 構成と K スペクトル」は trunk-concepts.txt にない（trunk は「H K 理論/K 空間と K スペクトル」）。(1) cubical Λ・Serre 鎖区間／鎖立方体・simplexHA*・simplexSubset*（native dg nerve と Λ からの dg 関手の比較）は dg 神経へ、立方体の標準形（CubeFaceNormal など）・ConcreteCube・cubical sets の Day tensor は necklace と立方体へ送った。Serre 鎖（serreInterval, serreCube*）は「単体的鎖とシャッフル」でもよい。(2) dgOdot*（LT §1.2 の ⊙ の dg 模型、DGLaxQuotientEnd の冒頭に記載）と Cat^perf（perfectStableVertex/Object/Arrow、BGT (a) の定義域）・tammePerfectSequence・perfectIdentityLaxSequence・perfectInvariant* は「局所化不変量：lax 引き戻しと双加群」へ。Cat^perf と局所化不変量の定義そのものを置く幹の概念がなく、ここに仮置きした（幹に「Cat^perf と局所化不変量（定義）」を立てる候補）。perfectSemiorthogonalVerdierSequence と perfectVerdierRawSquare は Verdier 列へ。(3) dgGluing 軸・恒等 Hom gluing・逆回転は dg の貼り合わせへ。pointedTensor*・terminalPath*・pointedKanLoop*・coaugmented* は基点付き対象へ。(4) 一般の単体的圏の事実（coherentEndpointPath、coherentSimplexArrow、coherentTriangleMappingEdge、CoherentSquareMappingTriangles、enrichedFunctorCollage*、SimplicialSSetDiagram、SSetInternalObject）は単体的圏と coherent 神経へ送った。一回目は「Path の分割」を（補助）coherent 化に含めているので、そちらに合わせるなら戻す。(5) 二重単体集合の対角（simplicialDiagonalFunctor、diagonalAssembly、diagonalZeroColumn、simplicialCylinderDiagonal、elementsResolution）は S 構成に固有でないので単体集合（基本）へ。「図式と二重単体集合のモデル構造」でもよい。(6) 重複の疑い：AssemblyInputArrow（Hom 両変数関手の要素の圏）はねじれ矢の圏と同じもの；terminalPathSpace / terminalPathHomotopyFiber は既存の path fibration・homotopy fiber と；pointedSSetSuspensionObject は既存の suspension と；triangulatedKZeroSourceMap は「完全複体と K₀」側の K₀ の関手性と。いずれも名前と docstring からの疑いで、相手の定義は確認していない。(7) 中断・未供給の部品：StableWideCofinalitySupply（Sp-7 の供給を仮定型として持つ Prop）、DGOdotMilnorIdentityLaxComparisonInput（未供給の比較を束ねる structure）、SingleRelativeComparison（供給境界）。(8) kOriginalSuspensionPrisms_pointed_simplicialCategory は local instance で概念ではない。(9) 本体まで開いたのは 13 ファイルの冒頭だけで、残りは docstring と signature で判断した。uncertain はその中でも判断が弱いもの。

## H K 理論/S 構成の入力（安定モデル・小さい Perf）（d54）

幹の名前「S 構成の入力（安定モデル・小さい Perf）」に合うのは 39 件中 25 件。dgHomGluing*（Hom_E(p(c),q(d)) の双加群、その cone 関手と逆 shift）6 件と DGOdotInput・PointedDGQuotientEndObject は Land–Tamme の ⊙（lax 引き戻し）の dg 模型の部品なので lax 引き戻しの概念へ。PointedKanObject・PointedKanInfinity・PointedSSetObject・PointedSpanDiagram は点つき単体集合の豊穣圏（BF の関手性の値域）で基点付き対象へ。EnrichedFunctorCollage は単体的豊穣関手の collage で単体的圏へ。dgKInputStableValue・dgKInputSpectrum・dgKInputSpectrumMap・dgKInputInfinity は presentedPerfectDG* / perfDGInputInfinity の別名（abbrev）で、言い換えの疑い。DGSmallPerfectBase・DGSmallPerfectArrowTarget も DGSmallPerfectEnvelope の特殊化の abbrev。dgSmallPerfectSquare*・DGSmallPerfectSquareGluing は LT 四角形用で、lax 引き戻し側に寄せる選択もある。

## H K 理論/pro 切除の塔（d55）

幹の名前「pro 切除の塔」に厳密に合うのは Tower・LevelHom・IsProIso・IsProZero の 7 件だけ。KST 4.16 の行列と単位化（firstBlockMatrix・blockColumn・integerUnitizationMap・integerUnitizationIdeal・IsCentralElement）と、Appendix A のモノイド作用（ActionObject・ActionProduct・setActionBar・SimplicialActionHom・SimplicialActionPairMap）は、d56 側の SimplicialMonoidAction・simplicialActionProduct・SimplicialSetAction・triangularBlockGroup と同じ話なので d56 へ。Appendix A の相対ホモロジー（relativeModule・relativeBarModule・SimplicialHomologyModel）と鎖区間はここに残したが、d55 と d56 の境目は機械的で、「pro の塔（一般論）」と「KST §4・付録 A の群ホモロジー計算」に切り直すほうが自然。SimplicialHomologyModel は借用したホモロジー関手を入力に取る構造体（界面）。obstructionDihedral は DihedralGroup 4 の abbrev。

## H K 理論/pro 切除：非単位環と GL（d56）

KST.Comparison.hatGLSpace・KST.Comparison.hatGLSubmonoid は単位的な単体環の ĜL_r（式 (2.2)）で、K 理論の模型の比較の側の定義だが、非単位版 NonUnitalSimplicialRing.hatGLSubmonoid と同じ概念なのでここに置いた（非単位版は単位版と整数成分の条件の交わり）。d55 にある ActionObject・ActionProduct・setActionBar・SimplicialActionHom・SimplicialActionPairMap・firstBlockMatrix・blockColumn・integerUnitization* はこちらへ移す案（d55 の notes）。受け入れ先は「単体的モノイドの作用と半直積」「三角ブロック群・列群と行列の作用」「非単位単体環と単位化によるイデアル模型」。

## H K 理論/導来 blowup（d57）

exteriorCochainInclusion・exteriorBaseChangeDifferential・exteriorProductDifferential・freeExteriorScalarMap は任意の d : M → R の外積 Koszul（総外積への包含、底変更、生成元の追加）で、blowup に固有でないので Koszul 複体へ。評価・制限・係数拡大は同じ構成が三系統ある：一般の図式の正規表示版 diagramAlgebra*（Evaluation・DerivedEvaluation・IteratedEvaluation・DerivedRestriction）、有限重なり版 finiteOverlap*（ModuleEvaluation・DerivedModuleEvaluation・IteratedModuleEvaluation・DerivedTransitionRestriction）、例外因子版 finiteOverlapExceptional*。条件も diagramAlgebraCartesianPerfect と diagramCartesianPerfect が並行で、重複の疑い（特殊化として一本にできるか要確認）。docstring に「候補模型」「層レベル Perf や dg 商との同値を主張しない」とあり、大域 Perf との比較は未完の経路。LiftedUniversalBase は宇宙の持ち上げ、FiniteOverlapIndex・ChartIndex は添字の型。

## H K 理論/導来幾何と係数層（d58）

幹の名前は「導来幾何」より「係数環層つきスキームの加群層と D_qc（Toën §3.2）」が中身に合う。DGResolution.Objects・Quotient・nullObjects は任意の dg 圏の cell 分解の後に Drinfeld 商を取る一般論（Objects は DGCategoryCellResolution.Source の abbrev）で dg 商へ。LinearComplex.mappingComplex・enrichment・mappingPostcompose は任意の線形加法圏の複体の dg 増強（mappingComplex は Mathlib の linearHomComplex の abbrev）で dg 圏へ。kInjectiveHomotopyObjects はホモトピー圏での acyclic の右直交（一般の K-injective）、moduleLocalizationR は加群の局所化の自己関手で、どちらも層に固有でない。CoefficientSheaf.Modules は SheafOfModules の abbrev、ResolvedComplexes は DGResolution.Objects の特殊化。QCoh（基礎加群が準連接）と hasQuasicoherentCohomology（D_qc）は docstring で区別されている。

## H K 理論/局所化不変量：Postnikov と平方零拡大（d59）

新しい小概念は不要で、102 件すべて一回目の 11 個に入った（全件、定義の本体とファイル冒頭の説明を読んだ。docstring があるのは 3 件だけ）。102 件中 58 件が足場：共通核 46 件、後続段の逆データ 12 件。重複：DGAlgebra.postnikovCommon*（n=1）は PostnikovCommonCore.postnikovCommon*（一般の n）に (n := 1) を入れただけの包みで、この一覧の中だけで同名の組が 9 組（RightZeroBase・RightClassToZero・RightImageToSecond・RightStandardClass・RightDenStandardClass・ClassTransitionTarget・ClassTransitionToZero・ClassRightDenominatorBase・RightGammaSourceWitness）、片方だけ一覧にある n=1 の包みも他に 7 件。同様に PostnikovTwoClassInverseData.*（numeratorLayer・sourceClass・rightClassifyingLayer・fixedRightCompletedClass・rightDenominatorCoefficientIso）は PostnikovSuccessorClassInverseData.* の同名の定義に (n := 1) と toSuccessor を入れた包み。ファイル冒頭に「旧 n=1 界面を保つ段階的移行」とあり、n=1 版は移行の残り。postnikovOneRoof*・postnikovTwoRoof*（一切断・二切断の roof の底変更）も n=1 固有の足場として共通核に入れた。cellPathNonpositiveSource/Projection/Comparison（4 回反復した cell 分解の connective cover）は胞体分解に入れたが、実質は共通核の経路の足場。connectiveCover（smart τ≤0 の dg 代数）は Postnikov 塔に入れた。SurjectiveRoof.value と connectiveValue は仮定（全ての準同型の反転／connective だけ）が違うだけの並行。postnikovClassModel と PostnikovSuccessorClassInverseData.originalTargetModel は同じ式（HomotopyPullbackModel.algebra (postnikovPerturbedClass …) (zeroSection …)）。postnikovInfinityCospan・quasiIsoInfinity は「局所化後の極限性はここでは主張しない」とあり、∞ 普遍性の経路は途中。

## H K 理論/局所化不変量：lax 引き戻しと双加群（d60）

名前空間 KST.LocalizingInvariants にあるだけで中身が別の概念の定義が 93 中 62。(1) Sp のホモトピー圏・整数 π 関手・fiber 四角形・二項積（SpectrumHo.*, NativeFiber.*, FiberModel.*, FiberDiagram*, Binary.*, NativeSplit.product, BinaryGraph.square など）は BF スペクトルの一般論なので G へ。FiberDiagram（fiber 四角形の圏）は pro の塔の対象として使われるので「pro 切除の塔」でもよい。(2) `local instance … : SimplicialCategory OmegaSpectrum := OmegaSpectrum.simplicialCategory` が名前違いで 8 個（intervalPathCategory, rightPresentationCategory, triangleCommutationCategory, fiberExactSimplicialCategory, arrowCalculusCategory, bfFiberSimplicialCategory, bfSquareSimplicialCategory, nativeTriangleCategory）。同じインスタンスの重複で、数学の概念ではない（G へ送った）。(3) 分母付き span（markedSpans, fixedMarkedSpans, fixedFractionEvaluation）は準圏の局所化の分数計算で C/局所化へ、verdierDenominatorOver・VerdierRecoveredQuotientCoconeCylinder・twoArrowSecondTarget・initialConeTensorCorner は Verdier 商の分数計算の足場で D/Verdier 列へ。completionCofiberWide は cofiber が本質像に入る辺の部分複体（冪等完備化の入力）で Verdier 列へ送ったが、C/冪等完備とモナド でもよい。(4) 双加群の 6 定義は使われ方がすべて Postnikov（「Postnikov と平方零拡大」側）。bimoduleRestrict は一般のモノイダル圏の Bimod なので B/双加群とテンソル へ移す案もある。幹の名前の「双加群」はこの 6 個だけを指し、lax 引き戻しとは独立。(5) tammeQuotient のファイル冒頭は「安定性・完全性・核の同定は後続」とあり候補の段階。laxDifferenceRho・LaxCounit・LaxUniversalDifference は一般商を恒等の lax 差へ比較する経路の部品。(6) MonoidPullback.obj/fst/snd（モノイド対象の pullback）は Z/モノイダル圏 へ、pullbackTower は pro の塔へ。

## H K 理論/降下（d61）

OrdinaryBarRelativeHomDescent.* の 5 定義（nativeFamily, choices, compositionComparison, compositionChoices, nativeRestrictionComparison）は名前の descent に規則が当たっただけで、中身はホモトピー関数複体の bar 分解の相対選択空間。ファイル冒頭に「中断した任意モデル源への一般化（計画書§396、分類B）」とあり中断した経路の部品。E/ホモトピー関数複体と分解 へ。残り 29 はすべて論文 §3（定理 3.1、補題 3.2・3.3）の降下。幾何の部品（有限型スキームの圏、被約閉部分スキーム、blowup の底変換）は A/スキーム・A/blowup と射影スキーム に近いが、降下の定義域として作られているのでここに残した。schemeReduction は一般のスキームの被約化で A/スキーム へ移してよい。closedCenterPullback（被約閉中心）と closedImmersionPullback（任意の閉埋め込み）は同じ構成の二版で重複の疑い。NaturalBlowupSequences は docstring に「実降下と L9 の列から供給する接続データ」とある明示入力の構造。

## H K 理論/非連結 K（d62）

MOVE は sequentialCandidateSimplicialCategory の 1 件（`SimplicialCategory OmegaSpectrum := OmegaSpectrum.simplicialCategory` の局所インスタンスの重複、d60 に同種が 8 個）。明示入力（docstring に「未供給」「明示入力」「供給待ち」とある構造・命題）：DGKappaConeInput, DGKappaPerfectInput, DGKappaSuspensionRelativeRoofInput, DGKappaSplitCofiberInput, DGSuspensionNativeActionInput, dgKappaNativeBFSquareComparison（Prop）, DGSuspensionStageProvider（「未構成の関数の型」）。dgKappaUnconditionalStageProvider・dgSuspensionUnconditionalIteration・dgNonconnectiveK は無条件版で、条件付き版（dgSuspensionNativeCandidate, dgSuspensionNativeSequence, dgSuspensionNativeSequenceStage, dgSuspensionSuppliedBFStructureEdge）と二重になっている疑い。sequentialSpectrum と sequentialLevelColimitSpectrum は BF 置換の前後で同じ逐次余極限の二版。逐次余極限の 7 定義（SpectrumSequence ほか）は BF スペクトルの一般論で G/Ω スペクトル に置いてもよいが、非連結化の入力として作られているので残した。dgKInputIndCompletion ほか「Indω と compact 生成」の 3 定義は C/空間・Cat∞・前層・Ind の応用（K-7 d4）。
