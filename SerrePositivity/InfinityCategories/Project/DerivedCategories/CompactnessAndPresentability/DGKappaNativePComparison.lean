module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.NativeArrowRelativeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.NativeDiagramFamilyReplacement
public import SerrePositivity.KST.NonConnective.DGKappaResolvedYonedaEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactMapPinchedPath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices

/-!
概要：元の P の包含比較を、同じ ν 値間の完全関手と境界固定の比較へ束ねる。
方針：既存の元の P 比較を保持し、その実 core 辺を両端固定の区間 Hom へ送る。
規約：実評価 Morita 比較の全入力族はここで仮定から除去しない。
使われ方：D-8 e の先行する Morita 全族から、元の P の全入力族への復帰。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (P : DGKappaPerfectInput R D I)

/-- 元の P と元の Yoneda の全合成を、同じ固定 ν 値間の完全関手として保持する。 -/
def dgKappaNativePExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R D)
    (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I)) where
  hom := (presentedPerfectDGQCatEvaluationEquivalence R D).hom ≫
    dgKappaPerfectResolvedComparison R D I P ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaResolvedKernelKInput R D I)) ≫
    (presentedPerfectDGQCatEvaluationEquivalence R (dgKappaResolvedKernelKInput R D I)).inv
  isExact := by
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgKappaResolvedKernelPerfEquivalence R D I P).hom.val :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
        (dgKappaResolvedKernelPerfQCatEquivalence R D I P).isQCatEquivalence
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso
      (dgKappaResolvedYonedaFixedPerfComparison R D I P).symm

/-- 元の同じ実評価 Morita 逆作用の完全関手。 -/
def dgKappaNativeMoritaExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R D)
    (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I)) where
  hom := (dgKappaResolvedKernelPerfEquivalence R D I P).hom.val
  isExact := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (dgKappaResolvedKernelPerfQCatEquivalence R D I P).isQCatEquivalence

/-- 元の実評価 Morita 比較の辺は、固定 ν の源内でも可逆。 -/
lemma dgKappaNativeMoritaExactMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeMoritaExactMap R D I P)) := by
  let e := dgKappaResolvedKernelPerfQCatEquivalence R D I P
  let g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))
      (dgKInputStableValue R D) :=
    ⟨e.inv, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse
    (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{max (u + 1) v}) (dgKappaNativeMoritaExactMap R D I P) g
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapCoreVertexIso e.homInvIso
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapCoreVertexIso e.invHomIso

/-- 元の指定 P 比較に対応する、同じ ν 両端を固定した写像空間内の実辺。 -/
def dgKappaNativePComparisonEdge : SSet.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativePExactMap R D I P)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeMoritaExactMap R D I P))) := by
  let h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaNativePExactMap R D I P).hom
      (dgKappaNativeMoritaExactMap R D I P).hom :=
    dgKappaResolvedYonedaFixedPerfComparison R D I P
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapPinchedPath
    (F := dgKappaNativePExactMap R D I P)
    (G := dgKappaNativeMoritaExactMap R D I P) h).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R D))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))))
  have hv (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R D)
      (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableArrowPinchedVertex F) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_vertex]
    congr 1
  exact e.ofEq (hv _) (hv _)

/-- 元の P 比較を境界固定の相対延長へ渡す、同じ実比較 path。 -/
def dgKappaNativePComparisonPath :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v})) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeArrowRelativePath (dgKappaNativePComparisonEdge R D I P)

lemma dgKappaNativePComparisonPath_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
        (dgKappaNativePComparisonPath R D I P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativePExactMap R D I P)).edge) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeArrowRelativePath_zero _

lemma dgKappaNativePComparisonPath_one :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
        (dgKappaNativePComparisonPath R D I P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeMoritaExactMap R D I P)).edge) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeArrowRelativePath_one _

lemma dgKappaNativePComparisonPath_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre (boundary 1).ι).app
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v})).app (Opposite.op ⦋0⦌)
        (dgKappaNativePComparisonPath R D I P) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R D))
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeArrowRelativePath_boundary _

/-- 先行する同じ実 Morita 全族から、元の P の包含と指定比較の全族を実構成する。
両 ν 端は全単体で固定し、各入力の指定比較 path 自体を厳密に回収する。 -/
lemma dgKappaNativePFamily_exists
    (s : DGSuspensionStageProvider.{u, v} R κ)
    (M : dgKInputInfinity.{u, max (u + 1) v} R ⟶
      (ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v})
    (hM : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
      M.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect)).edge)) :
    ∃ L : dgKInputInfinity.{u, max (u + 1) v} R ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v}),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre (boundary 1).ι).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v}) =
        (M ≫ (pre (boundary 1).ι).app _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 = M ∧
      (∀ A : PerfDGInput.{u, max (u + 1) v} R,
        L.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
          dgKappaNativePComparisonPath R A (s A).cone (s A).perfect) ∧
      (∀ A : PerfDGInput.{u, max (u + 1) v} R,
        (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
            (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativePExactMap R A (s A).cone (s A).perfect)).edge)) := by
  let a := fun k : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌ =>
    dgKappaNativePComparisonPath R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)
      (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)).cone (s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject k)).perfect
  have hav (A : PerfDGInput.{u, max (u + 1) v} R) :
      a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = dgKappaNativePComparisonPath R A (s A).cone (s A).perfect := by
    dsimp only [a]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject_vertex]
  have ha : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre (boundary 1).ι).app
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v})).app (Opposite.op ⦋0⦌) (a k) =
      ((M ≫ (pre (boundary 1).ι).app _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _).app
        (Opposite.op ⦋0⦌) k := by
    intro k
    obtain ⟨A, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv
      (PerfDGInput.{u, max (u + 1) v} R)).surjective k
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre (boundary 1).ι).app
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v})).app (Opposite.op ⦋0⦌)
        (a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) =
      ((M ≫ (pre (boundary 1).ι).app _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)
    rw [hav, dgKappaNativePComparisonPath_boundary]
    change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _).app (Opposite.op ⦋0⦌)
      (((pre (boundary 1).ι).app _).app (Opposite.op ⦋0⦌)
        (M.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)))
    rw [hM]
    congr 1
    have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect))).property
    change ((pre (boundary 1).ι).app _).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect)).edge)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _ 0 at hv
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hv
    exact hv.symm
  have hf : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (a k) =
      M.app (Opposite.op ⦋0⦌) k := by
    intro k
    obtain ⟨A, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv
      (PerfDGInput.{u, max (u + 1) v} R)).surjective k
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
      (a (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = M.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)
    rw [hav, dgKappaNativePComparisonPath_one, hM]
  obtain ⟨L, hb, hL, hv⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeDiagramFamily_relativeReplacement (boundary 1).ι M a ha hf
  refine ⟨L, hb, hL, ?_, ?_⟩
  · intro A
    exact (hv _).trans (hav A)
  · intro A
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
      (L.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
    rw [hv, hav, dgKappaNativePComparisonPath_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
