module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryFillerLifting

/-!
概要：実核零化面の同じ商合成を、全高次の境界を充填できる零図式空間へ置く。
方針：同じ指定商比較で全零性を回収し、完全関手圏の終対象の可縮性を使用する。
規約：商合成の可縮な比較空間を構成し、全四角形への相対延長は別に行う。
使われ方：指定三境界を保つ VerdierSquareDiagramIso の高次整合性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元の実核包含と元 cell 商辺の同じ固定 ν 合成。
方針：構成済みの二つの完全射をそのまま合成する。
規約：完備化後の指定射影へ置換しない。使われ方：実零化の対角合成。 -/
def dgOdotMilnorNuNullComposite : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Src) (Q) where
  hom := (dgOdotMilnorFlatKernelExactMap R d).hom ≫
    (dgOdotMilnorCellProjectionExactMap R d).hom
  isExact := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

/-- 概要：同じ実商合成は全対象を零対象へ送る。
方針：指定商比較で同じ完備化付き列の実零化を戻す。
規約：元の実商辺を保持する。使われ方：零図式の全高次比較空間。 -/
lemma dgOdotMilnorNuNullComposite_zero (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
    (x : (Src).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgOdotMilnorNuNullComposite R d).hom.app (Opposite.op ⦋0⦌) x) := by
  have hz := (dgOdotMilnorNuPerfectSequence R d h).projection_kills_inclusion x
  have e := (dgOdotMilnorNuPerfectProjectionComparison R d h).precomp
    (dgOdotMilnorFlatKernelExactMap R d).hom
  exact hz.of_vertexIso (e.app x).symm

/-- 概要：同じ始域・終域の完全関手圏の終対象からなる全比較空間。
方針：既存の終対象全部分複体を使用する。
規約：ホモトピー圏の同型集合へ切り詰めない。使われ方：高次零合成充填。 -/
abbrev DGOdotMilnorNuNullCoherenceSpace :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Q) : SSet.{u + 1}) : SSet.{u + 1})

/-- 概要：同じ実零合成を含む比較空間は全境界を充填する可縮 Kan 複体。
方針：全零性による点ごとの終対象性を充満部分関手圏へ反映する。
規約：同じ実合成の証拠を使い、追加の収縮や自然性を仮定しない。
使われ方：実零化面の相対三次元充填の入力。 -/
lemma dgOdotMilnorNuNullCoherenceSpace_contractible (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (DGOdotMilnorNuNullCoherenceSpace R d) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (Src) (Q) (dgOdotMilnorNuNullComposite R d), ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullComposite R d).hom)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
    (fun x => (dgOdotMilnorNuNullComposite_zero R d h x).2)

/-- 概要：同じ実商合成を可縮な比較空間の頂点として保持する。
方針：既証の全零性を完全関手圏の終対象性へ反映する。
規約：頂点の実関手を変更しない。使われ方：相対充填の固定端点。 -/
def dgOdotMilnorNuNullCompositeVertex (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (Src) (Q) (dgOdotMilnorNuNullComposite R d), ?_⟩
  intro v
  have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst v
  rw [op_id, CategoryTheory.Functor.map_id_apply]
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullComposite R d).hom)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
    (fun x => (dgOdotMilnorNuNullComposite_zero R d h x).2)

/-- 概要：同じ実零角を経由する二辺の固定 ν 合成。
方針：元の全対象商への射と指定延長の完全射を合成する。
規約：標準零圏への因子分解に置換しない。使われ方：実零化面のもう一方の経路。 -/
def dgOdotMilnorNuNullTopComposite : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Src) (Q) where
  hom := (dgKInputNuMap R (dgFixedNullLeft R
    (A := dgOdotMilnorFlatKernelInput R d))).hom ≫
    (dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).hom
  isExact := @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _
    (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _ _ from dgKInputNuMap R
      (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))).isExact
    (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _ _ from dgKInputNuMap R
      (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).isExact

/-- 概要：実零角経由の同じ合成は全対象を零対象へ送る。
方針：同じ零角の全零性と元の上辺の完全性を使う。
規約：元の商延長を保持する。使われ方：二経路を同じ比較空間へ置く。 -/
lemma dgOdotMilnorNuNullTopComposite_zero (x : (Src).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgOdotMilnorNuNullTopComposite R d).hom.app (Opposite.op ⦋0⦌) x) := by
  haveI := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap _ _ from dgKInputNuMap R
    (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).isExact
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero
    (F := (dgKInputNuMap R
      (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).hom) _
    (dgFixedNullInput_isZeroCategory R _ _)

/-- 概要：実零角を経由する同じ合成を全比較空間へ置く。
方針：全零性による終対象性を反映し、同じ関手の頂点を保持する。
規約：元の零角経由の二辺を変更しない。使われ方：実面の第二の固定端点。 -/
def dgOdotMilnorNuNullTopCompositeVertex :
    DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (Src) (Q) (dgOdotMilnorNuNullTopComposite R d), ?_⟩
  intro v
  have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst v
  rw [op_id, CategoryTheory.Functor.map_id_apply]
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullTopComposite R d).hom)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
    (fun x => (dgOdotMilnorNuNullTopComposite_zero R d x).2)

/-- 概要：実核面の二つの元合成を全比較空間の実辺で結ぶ。
方針：同じ可縮空間の終対象性による辺を取る。
規約：実面の指定二単体との比較は別に行う。使われ方：相対充填の端点データ。 -/
def dgOdotMilnorNuNullCompositeEdge (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      (dgOdotMilnorNuNullCompositeVertex R d h)
      (dgOdotMilnorNuNullTopCompositeVertex R d) :=
  Edge.ofTruncated (((dgOdotMilnorNuNullCoherenceSpace_contractible R d h).isTerminalVertex
    (dgOdotMilnorNuNullTopCompositeVertex R d)).nonempty_edge
      (dgOdotMilnorNuNullCompositeVertex R d h)).some

/-- 概要：可縮な実零合成空間の境界データを任意の単射に沿って延長する。
方針：境界充填からの既存の全単射持ち上げを特殊化する。
規約：境界データそのものを固定する。使われ方：実面比較の全パラメータ充填。 -/
def dgOdotMilnorNuNullCoherenceExtension (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
    {U V : SSet.{u + 1}} (i : U ⟶ V) [Mono i]
    (a : U ⟶ DGOdotMilnorNuNullCoherenceSpace R d) :
    V ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  SimplicialModel.BoundaryFillerLifting.extend
    (dgOdotMilnorNuNullCoherenceSpace_contractible R d h) i a

/-- 概要：実零合成空間への延長は元の全境界を厳密に保つ。
方針：同じ既存の延長の制限式を使用する。
規約：頂点だけの一致ではない。使われ方：指定境界を保つ相対面比較。 -/
lemma dgOdotMilnorNuNullCoherenceExtension_restriction (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
    {U V : SSet.{u + 1}} (i : U ⟶ V) [Mono i]
    (a : U ⟶ DGOdotMilnorNuNullCoherenceSpace R d) :
    i ≫ dgOdotMilnorNuNullCoherenceExtension R d h i a = a :=
  SimplicialModel.BoundaryFillerLifting.extend_initial
    (dgOdotMilnorNuNullCoherenceSpace_contractible R d h) i a

end SerrePositivity.KST.SConstruction
