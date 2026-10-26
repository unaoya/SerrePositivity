module
public import SerrePositivity.InfinityCategories.Derived.NativeArrowRelativeComparison
public import SerrePositivity.InfinityCategories.Derived.NativeDiagramFamilyReplacement
public import SerrePositivity.KST.NonConnective.DGKappaResolvedYonedaEvaluation
public import SerrePositivity.KST.LocalizingInvariants.ExactMapPinchedPath
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices

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
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (P : DGKappaPerfectInput R D I)

/-- 元の P と元の Yoneda の全合成を、同じ固定 ν 値間の完全関手として保持する。 -/
def dgKappaNativePExactMap : ExactMap (dgKInputStableValue R D)
    (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I)) where
  hom := (presentedPerfectDGQCatEvaluationEquivalence R D).hom ≫
    dgKappaPerfectResolvedComparison R D I P ≫
    dgNerve.map (dgPerfectYoneda R (dgKappaResolvedKernelKInput R D I)) ≫
    (presentedPerfectDGQCatEvaluationEquivalence R (dgKappaResolvedKernelKInput R D I)).inv
  isExact := by
    let : IsExactFunctor (dgKappaResolvedKernelPerfEquivalence R D I P).hom.val :=
      isExactFunctor_of_isQCatEquivalence
        (dgKappaResolvedKernelPerfQCatEquivalence R D I P).isQCatEquivalence
    exact isExactFunctor_of_functorIso
      (dgKappaResolvedYonedaFixedPerfComparison R D I P).symm

/-- 元の同じ実評価 Morita 逆作用の完全関手。 -/
def dgKappaNativeMoritaExactMap : ExactMap (dgKInputStableValue R D)
    (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I)) where
  hom := (dgKappaResolvedKernelPerfEquivalence R D I P).hom.val
  isExact := isExactFunctor_of_isQCatEquivalence
    (dgKappaResolvedKernelPerfQCatEquivalence R D I P).isQCatEquivalence

/-- 元の実評価 Morita 比較の辺は、固定 ν の源内でも可逆。 -/
lemma dgKappaNativeMoritaExactMap_isInvertible :
    IsInvertibleEdge (stableArrow (dgKappaNativeMoritaExactMap R D I P)) := by
  let e := dgKappaResolvedKernelPerfQCatEquivalence R D I P
  let g : ExactMap (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))
      (dgKInputStableValue R D) :=
    ⟨e.inv, isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence⟩
  apply coherentNerveEdge_isInvertible_of_enrichedInverse
    (C := StableQCat.{max (u + 1) v}) (dgKappaNativeMoritaExactMap R D I P) g
  · exact exactMapCoreVertexIso e.homInvIso
  · exact exactMapCoreVertexIso e.invHomIso

/-- 元の指定 P 比較に対応する、同じ ν 両端を固定した写像空間内の実辺。 -/
def dgKappaNativePComparisonEdge : SSet.Edge
    (intervalMappingVertexOfEdge (stableArrow (dgKappaNativePExactMap R D I P)))
    (intervalMappingVertexOfEdge (stableArrow (dgKappaNativeMoritaExactMap R D I P))) := by
  let h : FunctorIso (dgKappaNativePExactMap R D I P).hom
      (dgKappaNativeMoritaExactMap R D I P).hom :=
    dgKappaResolvedYonedaFixedPerfComparison R D I P
  let e := (exactMapPinchedPath
    (F := dgKappaNativePExactMap R D I P)
    (G := dgKappaNativeMoritaExactMap R D I P) h).map
    (pinchedHomToIntervalMappingSpace
      (stableVertex (dgKInputStableValue R D))
      (stableVertex (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))))
  have hv (F : ExactMap (dgKInputStableValue R D)
      (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))) :
      (pinchedHomToIntervalMappingSpace _ _).app (Opposite.op ⦋0⦌)
          (stableArrowPinchedVertex F) = intervalMappingVertexOfEdge (stableArrow F) := by
    rw [pinchedHomToIntervalMappingSpace_vertex]
    congr 1
  exact e.ofEq (hv _) (hv _)

/-- 元の P 比較を境界固定の相対延長へ渡す、同じ実比較 path。 -/
def dgKappaNativePComparisonPath :
    (equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
      StableInfinity.{max (u + 1) v})) _⦋0⦌ :=
  nativeArrowRelativePath (dgKappaNativePComparisonEdge R D I P)

lemma dgKappaNativePComparisonPath_zero :
    (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
        (dgKappaNativePComparisonPath R D I P) =
      functorVertex (SSet.yonedaEquiv.symm (stableArrow (dgKappaNativePExactMap R D I P)).edge) :=
  nativeArrowRelativePath_zero _

lemma dgKappaNativePComparisonPath_one :
    (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
        (dgKappaNativePComparisonPath R D I P) =
      functorVertex
        (SSet.yonedaEquiv.symm (stableArrow (dgKappaNativeMoritaExactMap R D I P)).edge) :=
  nativeArrowRelativePath_one _

lemma dgKappaNativePComparisonPath_boundary :
    (equivalencePathMap ((pre (boundary 1).ι).app
      StableInfinity.{max (u + 1) v})).app (Opposite.op ⦋0⦌)
        (dgKappaNativePComparisonPath R D I P) =
      (equivalencePathRefl _).app (Opposite.op ⦋0⦌)
        (functorVertex (intervalMappingBoundary
          (stableVertex (dgKInputStableValue R D))
          (stableVertex (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))))) :=
  nativeArrowRelativePath_boundary _

/-- 先行する同じ実 Morita 全族から、元の P の包含と指定比較の全族を実構成する。
両 ν 端は全単体で固定し、各入力の指定比較 path 自体を厳密に回収する。 -/
lemma dgKappaNativePFamily_exists
    (s : DGSuspensionStageProvider.{u, v} R κ)
    (M : dgKInputInfinity.{u, max (u + 1) v} R ⟶
      (ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj StableInfinity.{max (u + 1) v})
    (hM : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
      M.app (Opposite.op ⦋0⦌) (coherentNerveVertex A) = functorVertex
        (SSet.yonedaEquiv.symm
          (stableArrow (dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect)).edge)) :
    ∃ L : dgKInputInfinity.{u, max (u + 1) v} R ⟶
        equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
          StableInfinity.{max (u + 1) v}),
      L ≫ equivalencePathMap ((pre (boundary 1).ι).app StableInfinity.{max (u + 1) v}) =
        (M ≫ (pre (boundary 1).ι).app _) ≫ equivalencePathRefl _ ∧
      L ≫ equivalencePathEndpoint _ 1 = M ∧
      (∀ A : PerfDGInput.{u, max (u + 1) v} R,
        L.app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
          dgKappaNativePComparisonPath R A (s A).cone (s A).perfect) ∧
      (∀ A : PerfDGInput.{u, max (u + 1) v} R,
        (L ≫ equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
          functorVertex (SSet.yonedaEquiv.symm
            (stableArrow (dgKappaNativePExactMap R A (s A).cone (s A).perfect)).edge)) := by
  let a := fun k : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌ =>
    dgKappaNativePComparisonPath R (coherentNerveObject k)
      (s (coherentNerveObject k)).cone (s (coherentNerveObject k)).perfect
  have hav (A : PerfDGInput.{u, max (u + 1) v} R) :
      a (coherentNerveVertex A) = dgKappaNativePComparisonPath R A (s A).cone (s A).perfect := by
    dsimp only [a]
    rw [coherentNerveObject_vertex]
  have ha : ∀ k, (equivalencePathMap ((pre (boundary 1).ι).app
      StableInfinity.{max (u + 1) v})).app (Opposite.op ⦋0⦌) (a k) =
      ((M ≫ (pre (boundary 1).ι).app _) ≫ equivalencePathRefl _).app
        (Opposite.op ⦋0⦌) k := by
    intro k
    obtain ⟨A, rfl⟩ := (coherentNerveVertexEquiv
      (PerfDGInput.{u, max (u + 1) v} R)).surjective k
    change (equivalencePathMap ((pre (boundary 1).ι).app
      StableInfinity.{max (u + 1) v})).app (Opposite.op ⦋0⦌)
        (a (coherentNerveVertex A)) =
      ((M ≫ (pre (boundary 1).ι).app _) ≫ equivalencePathRefl _).app
        (Opposite.op ⦋0⦌) (coherentNerveVertex A)
    rw [hav, dgKappaNativePComparisonPath_boundary]
    change _ = (equivalencePathRefl _).app (Opposite.op ⦋0⦌)
      (((pre (boundary 1).ι).app _).app (Opposite.op ⦋0⦌)
        (M.app (Opposite.op ⦋0⦌) (coherentNerveVertex A)))
    rw [hM]
    congr 1
    have hv := (intervalMappingVertexOfEdge
      (stableArrow (dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect))).property
    change ((pre (boundary 1).ι).app _).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm
        (stableArrow (dgKappaNativeMoritaExactMap R A (s A).cone (s A).perfect)).edge)) =
        PinchedHom.constant _ 0 at hv
    rw [pinchedConstant_zero] at hv
    exact hv.symm
  have hf : ∀ k, (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (a k) =
      M.app (Opposite.op ⦋0⦌) k := by
    intro k
    obtain ⟨A, rfl⟩ := (coherentNerveVertexEquiv
      (PerfDGInput.{u, max (u + 1) v} R)).surjective k
    change (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
      (a (coherentNerveVertex A)) = M.app (Opposite.op ⦋0⦌) (coherentNerveVertex A)
    rw [hav, dgKappaNativePComparisonPath_one, hM]
  obtain ⟨L, hb, hL, hv⟩ :=
    nativeDiagramFamily_relativeReplacement (boundary 1).ι M a ha hf
  refine ⟨L, hb, hL, ?_, ?_⟩
  · intro A
    exact (hv _).trans (hav A)
  · intro A
    change (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
      (L.app (Opposite.op ⦋0⦌) (coherentNerveVertex A)) = _
    rw [hv, hav, dgKappaNativePComparisonPath_zero]

end SerrePositivity.InfinityCategories
