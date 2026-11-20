"""概念の木の幹（下書き 1、2026-11-20）。型に現れる回数の多い定義 320 個を読んで、概念の名前と親子を付けたもの。
RULES は (概念, 正規表現) の列で、上から順に候補の完全名に当てる。320 個に付けた名前を、同じ概念の他の候補にも広げるために正規表現にしてある。
木は「大分類 / 概念」の二段。名前は内容から付けた（ディレクトリの名前ではない）。"""
RULES = [
 # A 可換代数・数論幾何（主定理の本体）
 ('A 可換代数と数論幾何/δ 環', r'DeltaStructure|[dD]elta(Adjoin|Division|Closure)|RelativeFreeDeltaRing|relativeFreeDelta|RankOneDelta'),
 ('A 可換代数と数論幾何/プリズム', r'OrientedPrism|IsBoundedPrism|Prismatic\.'),
 ('A 可換代数と数論幾何/パーフェクトイド', r'Perfectoid|powerRoot|PowerRoot'),
 ('A 可換代数と数論幾何/根の塔', r'Section2\.(tower|Tower)|RootTower'),
 ('A 可換代数と数論幾何/正規化長さ', r'NormalizedLength|LengthAlgebra'),
 ('A 可換代数と数論幾何/導来完備化', r'DerivedCompletion|boundedAboveDerived'),
 ('A 可換代数と数論幾何/完全複体と K₀', r'PerfectHomotopy|perfectHomotopy|triangulatedK0|K0WithSupport|G0WithSupport'),
 ('A 可換代数と数論幾何/Rees 代数と進完備', r'reesAdic|Rees'),
 ('A 可換代数と数論幾何/スキーム', r'FiniteTypeSchemes|AlgebraicGeometry\.'),
 # H K 理論（B〜G より先に当てる：名前に dg や Spectrum を含むため）
 ('H K 理論/pro 切除の塔', r'ProExcision\.'),
 ('H K 理論/局所化不変量：Postnikov と平方零拡大', r'LocalizingInvariants\.(DGAlgebra|SquareZero|Path)'),
 ('H K 理論/局所化不変量：lax 引き戻しと双加群', r'LocalizingInvariants\.'),
 ('H K 理論/S 構成の入力（安定モデル・小さい Perf）', r'SConstruction\.(StableModel|PerfDGInput|DGOdotInput|SmallBundled|DGSmallPerfect|dgSmallPerfect|dgHomGluing|dgKInput|PreservesCofiber|perfectStableInfinity|Pointed)'),
 ('H K 理論/K 空間と K スペクトル', r'SConstruction\.(kOmega|kKan)|SConstruction\.'),
 ('H K 理論/非連結 K', r'NonConnective\.'),
 ('H K 理論/降下', r'KST\.Descent\.'),
 # G スペクトル
 ('G スペクトル/Ω スペクトル（Bousfield–Friedlander）', r'KST\.Spectra\.'),
 ('G スペクトル/対称列', r'SymmetricSequence|FiniteBijection|TensorPowers'),
 ('G スペクトル/対称スペクトル', r'SymmetricSpectrum'),
 # F E∞
 ('F オペラドと E∞/dg オペラドと代数', r'DGOperads\.|Operad'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', r'BarrattEccles|Surjection|SimplexCuts|IntervalCuts'),
 # E モデル圏
 ('E モデル圏/Reedy', r'Reedy\.'),
 ('E モデル圏/ホモトピー関数複体と分解', r'HomotopyFunctionComplex|CosimplicialHom|Resolution(Object|Arrow)'),
 ('E モデル圏/単体的モデルと anodyne', r'SimplicialModel|[aA]nodyne'),
 # D 安定・導来 ∞ 圏
 ('D 安定 ∞ 圏と導来 ∞ 圏/Verdier 列', r'Verdier(Diagram|Sequence)|IsVerdier'),
 ('D 安定 ∞ 圏と導来 ∞ 圏/安定 ∞ 圏', r'Stable(Category|Infinity|QCat)|IsStable|ExactMap|ZeroTriangle|ZeroObjects|IsZeroVertex|loopDiagrams|cofiber'),
 ('D 安定 ∞ 圏と導来 ∞ 圏/dg 代数（一対象 dg 圏）', r'DGAlgebraPoint|dgAlgebra(Category|Map)'),
 ('D 安定 ∞ 圏と導来 ∞ 圏/導来 ∞ 圏', r'derivedInfinityCategory|DerivedInfinityCat|dgModule(Nerve|Semifree|Derived)|SemifreeDGModules|complexSemifree|IsDGPretriangulated|complexPinchedSpace|DGFunctorComma|DGModuleFunctorResolution'),
 ('D 安定 ∞ 圏と導来 ∞ 圏/dg の貼り合わせ', r'Gluing\.'),
 # C ∞ 圏
 ('C 単体集合と ∞ 圏/dg 神経', r'DifferentialGradedCategories\.|dgNerve|Simplex\.vertex|Functor\.map'),
 ('C 単体集合と ∞ 圏/結とスライス', r'SliceAndJoin|join|slice(Under|Over)|relativeJoin'),
 ('C 単体集合と ∞ 圏/極限と余極限', r'LimitsAndColimits|Join(Cocone|Cone)|Is(Colimit|Limit)Cone|pullbackCospan|KanExtensions|bousfieldKan'),
 ('C 単体集合と ∞ 圏/ファイブレーションと straightening', r'Fibration|vertexFiber|[uU]nstraighten|[sS]traighten|TransportSimplex|CovariantTransport|weightedNer'),
 ('C 単体集合と ∞ 圏/写像空間', r'MorphismSpaces|[pP]inchedHom|intervalMapping'),
 ('C 単体集合と ∞ 圏/単体的圏と coherent 神経', r'SimplicialCategories|coherentNerve|strictCoherentDiag'),
 ('C 単体集合と ∞ 圏/空間・Cat∞・前層・Ind', r'InfinityCategoryQC|SpaceInfinity|CatInfinity|KanObject|QCat$|PresheafInfinity|YonedaEmbedding|IndInfini|indYoneda'),
 ('C 単体集合と ∞ 圏/局所化（Dwyer–Kan）', r'Localization\.|WordAppend|Word\.'),
 ('C 単体集合と ∞ 圏/関手単体集合と同値', r'functorVertex|FunctorIso|IsQCatEquiva|QCatEquivale|VertexIso|IsInvertibleEdg|quasicategoryCo|evaluateFunctorAt|relativeFunc|functorEdge|FunctorHom|Equivalence\.|IsPrecompositionEquivalence|hfulAndEssentiallySurjective|FaithfulAndEssentiallySurjective'),
 ('C 単体集合と ∞ 圏/基点付き対象', r'PointedObject|PointedSimplicialSet|PointedSimplicialSets'),
 ('C 単体集合と ∞ 圏/Kan 複体とホモトピー群', r'KanComplex|HomotopyGroup|KanPi|IsWeakHomoto|IsSimplicial|prismEndpoint|ConcreteCube|simplicialHo|kanDiagram|UniverseLiftFillers|CoherentArrowString|HigherHomotopyCategories'),
 ('C 単体集合と ∞ 圏/冪等完備とモナド', r'Idempotent|Monads\.'),
 # B dg
 ('B 複体と dg 圏/dg 商と cell 分解', r'DGQuotient|CellResolution|DGCellAttachment'),
 ('B 複体と dg 圏/双加群とテンソル', r'Bimodule|BalancedTensor|KFlat'),
 ('B 複体と dg 圏/導来圏と Perf（dg 加群）', r'Derived(Module)?Category|moduleToDerived|[pP]erfect|derivedFiniteCell|TriaCategory'),
 ('B 複体と dg 圏/dg 加群', r'RightModule|LeftModule|ModuleCategory|module(Hom|Cone|QuasiIso|Evaluation)|representable|ModuleHomotopyCategory'),
 ('B 複体と dg 圏/係数の取り替え', r'ScalarExtension'),
 ('B 複体と dg 圏/dg 圏と dg 関手', r'DGCategory|DGFunctor|GradedHom|homObject|ClosedCategory|DifferentialGraded\.(compose|HomotopyCategory|boundaryRelation|EndomorphismObject|DGTensorCategory)'),
 ('B 複体と dg 圏/複体', r'DifferentialGraded\.(Complex|homComplex|zeroCycles)|cochainTensor|ComplexLimits|HomologicalAlgebra'),
]
