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
 ('C 単体集合と ∞ 圏/結とスライス', r'SliceAndJoin|(?<!d)[jJ]oin(?!t)|slice(Under|Over)'),
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
 ('B 複体と dg 圏/導来圏と Perf（dg 加群）', r'Derived(Module)?Category|moduleToDerived|PerfectDG|[pP]erfectOver|PerfectModule|derivedFiniteCell|TriaCategory|DifferentialGraded\..*[pP]erfect'),
 ('B 複体と dg 圏/dg 加群', r'RightModule|LeftModule|ModuleCategory|module(Hom|Cone|QuasiIso|Evaluation)|representable|ModuleHomotopyCategory'),
 ('B 複体と dg 圏/係数の取り替え', r'ScalarExtension'),
 ('B 複体と dg 圏/dg 圏と dg 関手', r'DGCategory|DGFunctor|GradedHom|homObject|ClosedCategory|DifferentialGraded\.(compose|HomotopyCategory|boundaryRelation|EndomorphismObject|DGTensorCategory)'),
 ('B 複体と dg 圏/複体', r'DifferentialGraded\.(Complex|homComplex|zeroCycles)|cochainTensor|ComplexLimits|HomologicalAlgebra'),
]

# 版 2（11-20）：未割り当ての宣言の型に多く現れる定義 260 個を読んで足した概念。RULES より先に当てる。
RULES2 = [
 ('A 可換代数と数論幾何/Čech 複体と被覆', r'[cC]ech'),
 ('A 可換代数と数論幾何/blowup と射影スキーム', r'AlgebraicGeometry\.(.*[bB]lowup|rees|Rees|.*[sS]egre|projective|chartBase|.*PureTransform|boundaryTorsion|affineCenter|matrixMinor|OpenAtlas|specIdeal)'),
 ('A 可換代数と数論幾何/Frobenius の順極限', r'[fF]robenius(Direct|Ring)|FrobeniusRing'),
 ('A 可換代数と数論幾何/分冪包絡とクリスタリン', r'Prismatic\.(pd|PD|Crys|Poly|CompletedPD)|PrincipalDP|principalDP'),
 ('A 可換代数と数論幾何/根の添加（André）', r'Andre\.|[mM]onicPowerFamily'),
 ('A 可換代数と数論幾何/p 基底', r'pPowerSubfield|IsPBasis|PExponent|pBasis'),
 ('A 可換代数と数論幾何/Koszul 複体', r'[kK]oszul'),
 ('A 可換代数と数論幾何/台つきの加群と Tor', r'TorModule|SupportedFGModule|finiteModuleSupported|supportPullback|scalarSupported|g0Supported'),
 ('A 可換代数と数論幾何/漸近的なランク', r'Asymptotic\.'),
 ('A 可換代数と数論幾何/de Rham 複体', r'DeRham\.'),
 ('A 可換代数と数論幾何/Hilbert–Samuel と対角線', r'HilbertSamuel|DiagonalRing'),
 ('B 複体と dg 圏/複体', r'^SerrePositivity\.(smulId|scalarCone|baseChange|boundedHomotopy|IsResolutionOf|CochainIdempotent)'),
 ('B 複体と dg 圏/単体的鎖とシャッフル', r'linearized|Linearized|[iI]ntegerTensor|integerLinearization|ShuffleIndex|AlexanderWhitney|SimplicialChains|simplicialRingCoefficient'),
 ('C 単体集合と ∞ 圏/necklace と立方体（組合せ）', r'Necklace|necklace|SimplicialCombinatorics|SimplicialCategories\.(cube|pathThrough|hornObj)|CoherentResolution|coherentResolution'),
 ('C 単体集合と ∞ 圏/冪等完備とモナド', r'RetractsAndIdempotents|Walking(Idem|Split)|SplitShape|simplexPreserves'),
 ('C 単体集合と ∞ 圏/ファイブレーションと straightening', r'TwoSided(Grothendieck|Diagram|Elements)'),
 ('C 単体集合と ∞ 圏/極限と余極限', r'weighted(Sections|Colimit)|simplicialReplacement|squareTriangle|pastingCorner'),
 ('C 単体集合と ∞ 圏/サイズの条件', r'SizeConditions|IsKappaSmall'),
 ('C 単体集合と ∞ 圏/∞ 層', r'Sheaves\.'),
 ('C 単体集合と ∞ 圏/局所化（Dwyer–Kan）', r'FreeQuiverCover|FiniteQuiver|MarkedGeneratorPaths|LeafDeletion|HomotopyDiagramComparison|LeftTrivialThreeArrow'),
 ('C 単体集合と ∞ 圏/Kan 複体とホモトピー群', r'HomotopyGroups\.'),
 ('C 単体集合と ∞ 圏/結とスライス', r'Join\.(augObj|Simplex|pullCut)|fatJoin'),
 ('D 安定 ∞ 圏と導来 ∞ 圏/安定 ∞ 圏', r'Excision(Grid)'),
 ('E モデル圏/Quillen 関手と生成', r'Quillen\.|CofibrantlyGenerated|Smith\.|ArrowFactorization'),
 ('E モデル圏/図式と二重単体集合のモデル構造', r'DiagramModel|BisimplicialModel'),
 ('E モデル圏/語による分解（小対象の議論）', r'(Retract|Ambient|Segment)Words|WordSegment|NerveSimplexEndpoint|NerveBiparameter|NerveCoherentFamily|KanComparisonTriangle|RelativeChoiceSpace'),
 ('E モデル圏/ホモトピー関数複体と分解', r'OrdinaryBarFree|FreeGeneratorCategories|ComonadResolution'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', r'TableReduction|ShufflePath|AdjacentCollapse|BinaryTensorWord'),
 ('F オペラドと E∞/冪作用', r'PowerOperation|Coxeter'),
 ('G スペクトル/モノイダル圏の中の加群（一般論）', r'MonoidalBalancedTensor|MonoidalFreeModule|MonoidalModule|Enriched\.TensorCotensor|RepresentedMapping'),
 ('H K 理論/導来幾何と係数層', r'DerivedGeometry|CoefficientSheaf'),
 ('H K 理論/導来 blowup', r'DerivedBlowup'),
 ('H K 理論/pro 切除：非単位環と GL', r'ProExcision\.(NonUnital|Simplicial(Monoid|Set|Ideal)|triangularBlock|simplicialAction)|hatGL|columnGroup'),
 ('H K 理論/K 理論の模型の比較', r'KST\.Comparison\.'),
 ('H K 理論/S 構成の入力（安定モデル・小さい Perf）', r'SConstruction\.(EnrichedFunctorCollage|FamilyHomotopyChain|EndpointFixed|necklaceBead)'),
 ('H K 理論/K 空間と K スペクトル', r'SConstruction\.(Ar|arNerve|simplicialDiagonal)'),
 ('H K 理論/降下', r'Descent\.'),
]
# Mathlib の定義を根にする：本体の核が型に現れない宣言は、型に現れる Mathlib の定義のうち、この表で最初に当たるものの概念に入れる（上ほど特殊）
MATHLIB_ROOTS = [
 ('A 可換代数と数論幾何/スキーム', r'^AlgebraicGeometry\.'),
 ('E モデル圏/モデル圏（基本）', r'^HomotopicalAlgebra\.'),
 ('C 単体集合と ∞ 圏/準圏（基本）', r'^SSet\.Quasicategory'),
 ('C 単体集合と ∞ 圏/Kan 複体とホモトピー群', r'^SSet\.KanComplex|^SSet\.Homotopy|^SSet\.RelativeMorphism|^SSet\.HomotopyCategory'),
 ('C 単体集合と ∞ 圏/単体的圏と coherent 神経', r'^CategoryTheory\.SimplicialNerve|^CategoryTheory\.SimplicialCategory'),
 ('C 単体集合と ∞ 圏/神経', r'^CategoryTheory\.nerve|^CategoryTheory\.Nerve|^SSet\.Truncated'),
 ('C 単体集合と ∞ 圏/単体集合（基本）', r'^SSet(\.|$)|^SimplexCategory|^CategoryTheory\.(Simplicial|Cosimplicial)Object'),
 ('B 複体と dg 圏/複体', r'^CochainComplex|^HomologicalComplex|^ChainComplex|^ComplexShape|^CategoryTheory\.GradedObject|^HomotopyCategory|^DerivedCategory'),
 ('Z 圏論一般/豊穣圏', r'^CategoryTheory\.Enriched'),
 ('E モデル圏/局所化と射の類（通常の圏）', r'^CategoryTheory\.MorphismProperty|^CategoryTheory\.Localization'),
 ('Z 圏論一般/モノイダル圏', r'^CategoryTheory\.Monoidal|^CategoryTheory\.Mon(\.|$)|^CategoryTheory\.ihom|^CategoryTheory\.Braided|^CategoryTheory\.Symmetric'),
 ('A 可換代数と数論幾何/環と加群（その他）', r'^Ideal|^Algebra|^MvPolynomial|^Polynomial|^Module|^ModuleCat|^Submodule|^LinearMap|^CommRing|^Ring|^WittVector|^TensorProduct|^IsLocalization|^Localization|^AdicCompletion|^Field|^IntermediateField'),
 ('Z 圏論一般/圏・関手・極限', r'^CategoryTheory\.'),
 ('Z 圏論一般/組合せと順序', r'^Fin(\.|$)|^Finset|^List|^Equiv\.Perm|^OrderHom|^Set(\.|$)|^Nat|^Int'),
]

# 版 3（11-20）：受け皿（単体集合の基本、環と加群のその他、圏、組合せ）の中の定義を読んで足した概念。RULES2 より先に当てる。
RULES3 = [
 ('C 単体集合と ∞ 圏/表現可能 ∞ 圏とフィルター', r'PresentableI|FilteredI|PrLFunctor|PrRFunctor|Smith\.(Presentable|LocalPresentable)|FilteredExchange'),
 ('C 単体集合と ∞ 圏/ねじれ矢と余スパン', r'TwistedArrows'),
 ('C 単体集合と ∞ 圏/ファイブレーションと straightening', r'LeftAndRightFibrations|RightFibration|[aA]nodyneExtensions|cocartesianSections|transportSquare'),
 ('C 単体集合と ∞ 圏/極限と余極限', r'Is(Initial|Terminal)Vertex|HomotopyPushoutSquares|doubleMappingCylinder|IsHomotopyPullback|[sS]trictDiagram|simplicialSections'),
 ('C 単体集合と ∞ 圏/Kan 複体とホモトピー群', r'IsContractibleKan|TheExInfinityFunctor|KanHornFamily|continuousKanReplacement'),
 ('C 単体集合と ∞ 圏/写像空間', r'laxPullback'),
 ('C 単体集合と ∞ 圏/局所化（Dwyer–Kan）', r'AdjointFunctors\.Localization|InvertsEdges|MarkedSpine|UnmarkedGenerators'),
 ('C 単体集合と ∞ 圏/随伴（2 圏）', r'AdjunctionsInTwoCategories|[bB]icategory'),
 ('C 単体集合と ∞ 圏/冪等完備とモナド', r'Monads\.'),
 ('A 可換代数と数論幾何/Čech 複体と被覆', r'^SerrePositivity\.Cosimplicial\.'),
 ('A 可換代数と数論幾何/分冪包絡とクリスタリン', r'pdDeRham|Prismatic\.(pdRow|polynomialCech|crystalline|RelativePDEnvelope)|rankOneDP|pDivisionFactorial'),
 ('A 可換代数と数論幾何/完備平坦と整閉（環の性質）', r'IsCompletely|IsAbsolutelyIntegrallyClosed|IsUniversalHomeomorphism|GenericEtale|adicQuotientAlgebra'),
 ('A 可換代数と数論幾何/ほとんど数学とねじれ', r'Almost\.|IsPowTorsion|PowerTorsion'),
 ('A 可換代数と数論幾何/付値と区間', r'Valuation|intervalPrime'),
 ('A 可換代数と数論幾何/交点重複度と χ', r'^SerrePositivity\.chi$|IsSystemOfParameters|IntersectionMultiplicity'),
 ('A 可換代数と数論幾何/δ 環', r'FreeDeltaRing'),
 ('E モデル圏/図式と二重単体集合のモデル構造', r'DiagramModel\.'),
]
# Mathlib の根の追加（MATHLIB_ROOTS より先に当てる）
MATHLIB_ROOTS3 = [
 ('B 複体と dg 圏/三角圏', r'^CategoryTheory\.(Pretriangulated|Triangulated|HasShift)'),
 ('C 単体集合と ∞ 圏/随伴（2 圏）', r'^CategoryTheory\.Bicategory'),
 ('C 単体集合と ∞ 圏/単体的圏と coherent 神経', r'^CategoryTheory\.SimplicialThickening'),
 ('B 複体と dg 圏/単体的鎖とシャッフル', r'^AlgebraicTopology\.'),
]

# 版 4（11-20）：読む作業（split/c*.json）で分かった名前の規則の誤りを直す。RULES3 より先に当てる。
RULES4 = [
 ('H K 理論/K 空間と K スペクトル', r'KST\.Fibration\.'),
]
# 概念の名前の改め（読む作業の指摘）
RENAME = {
 'H K 理論/K 空間と K スペクトル': 'H K 理論/S 構成と K スペクトル',
 'C 単体集合と ∞ 圏/表現可能 ∞ 圏とフィルター': 'C 単体集合と ∞ 圏/表示可能 ∞ 圏とフィルター',
 'C 単体集合と ∞ 圏/随伴（2 圏）': 'C 単体集合と ∞ 圏/随伴（∞ 圏）',
}
# 読む作業で、小概念を別の概念として立てるもの：(元の概念, 小概念の名前の先頭) → 新しい概念
PROMOTE = [
 ('B 複体と dg 圏/導来圏と Perf（dg 加群）', 'coherent bar', 'D 安定 ∞ 圏と導来 ∞ 圏/coherent bar 構成'),
 ('B 複体と dg 圏/導来圏と Perf（dg 加群）', '（補助）coherent bar', 'D 安定 ∞ 圏と導来 ∞ 圏/coherent bar 構成'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', 'E 代数のモデル構造', 'F オペラドと E∞/E∞ 代数の圏（CAlg と加群）'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', '（補助）導来写像空間', 'F オペラドと E∞/E∞ 代数の圏（CAlg と加群）'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', 'CAlg', 'F オペラドと E∞/E∞ 代数の圏（CAlg と加群）'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', 'E 代数上の加群', 'F オペラドと E∞/E∞ 代数の圏（CAlg と加群）'),
 ('F オペラドと E∞/Barratt–Eccles と全射オペラド', '（補助）加群のテンソル', 'F オペラドと E∞/E∞ 代数の圏（CAlg と加群）'),
]

# 版 5（11-20）：二回目の読む作業（split2/d*.json）の指摘による改名と、小概念を別の概念として立てるもの
A_, B_, C_, D_, E_, G_, H_, Z_ = 'A 可換代数と数論幾何/', 'B 複体と dg 圏/', 'C 単体集合と ∞ 圏/', 'D 安定 ∞ 圏と導来 ∞ 圏/', 'E モデル圏/', 'G スペクトル/', 'H K 理論/', 'Z 圏論一般/'
RENAME.update({
 C_ + 'ねじれ矢と余スパン': C_ + 'ねじれ矢と edgewise subdivision',
 C_ + '冪等完備とモナド': C_ + '冪等完備',
 H_ + 'K 理論の模型の比較': H_ + '群完備化と plus 構成',
 E_ + '語による分解（小対象の議論）': E_ + '止めた経路：任意のモデル圏への一般化',
 E_ + '図式と二重単体集合のモデル構造': E_ + '図式のモデル構造とホモトピー余極限',
 H_ + '導来幾何と係数層': H_ + '係数環層つきスキームの加群層と D_qc',
 G_ + 'モノイダル圏の中の加群（一般論）': Z_ + 'モノイダル圏の中の加群',
 D_ + 'dg 代数（一対象 dg 圏）': B_ + 'dg 圏と dg 関手',
 A_ + 'Rees 代数と進完備': A_ + 'blowup と射影スキーム',
})
for _pre in ['自由随伴', '自己関手', 'Adj ', '（補助）有限順序']: PROMOTE.append((C_ + '冪等完備とモナド', _pre, C_ + '自由随伴（HA §4.7 の組合せ論）'))
for _pre in ['プリズマティック', 'Čech–Alexander', 'Hodge–Tate', '結晶被覆', '（補助）HT', '（補助）Witt']: PROMOTE.append((A_ + 'プリズム', _pre, A_ + 'プリズマティックコホモロジー'))
PROMOTE.append((A_ + '導来完備化', '有界上導来圏', A_ + '上に有界な導来圏と導来底変換'))
for _pre in ['δ 除算', 'p 完備 δ 除算']: PROMOTE.append((A_ + 'δ 環', _pre, A_ + 'δ 除算（prismatic envelope の部品）'))
