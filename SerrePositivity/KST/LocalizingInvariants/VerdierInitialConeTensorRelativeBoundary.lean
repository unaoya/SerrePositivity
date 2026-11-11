module

public import SerrePositivity.KST.LocalizingInvariants.SpecifiedBoundaryEdgeNormalization
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.RelativeComparisonInverse
public import SerrePositivity.KST.LocalizingInvariants.VerdierInitialConeTensorRelativeComparison

/-!
概要：元の図式側で定値な全境界比較から、その側を全時刻で固定する実延長を回収する。
方針：実境界辺のまま厳密化し、固定図式の fiber 内で二つの全比較を合成する。
規約：逆比較を全関手圏で再選択せず、元の実境界の定値性を保つ。
使われ方：c5 の次元帰納で、回収した尾部を次の全境界へ渡すための相対延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の図式側で定値な実境界比較は、その側を固定した実延長と全比較を与える。 -/
lemma exists_verdierInitialConeTensorRelativeBoundary {A₀ B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A₀ B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (A L : SSet.{u}) [A.Finite] [L.Finite]
    (p : initialConeTensorCorner A L ⟶ B.obj)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ C.obj)
    (a : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (initialConeTensorCornerInclusion A L ≫ H))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ q.hom))) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a)
    {O : SSet.{u}} (k : O ⟶ initialConeTensorCorner A L) [Mono k]
    (hk : ((pre k).app C.obj).app (Opposite.op ⦋1⦌) a.edge =
      (Truncated.Edge.id (X := (truncation 2).obj ((ihom O).obj C.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (k ≫ p ≫ q.hom))).edge) :
    ∃ (D : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) L ⟶ B.obj)
      (J : SSet.Homotopy (D ≫ q.hom) H),
      initialConeTensorCornerInclusion A L ≫ D = p ∧
      ((k ≫ initialConeTensorCornerInclusion A L) ▷ (Δ[1] : SSet.{u})) ≫ J.h =
        fst O Δ[1] ≫ (k ≫ p ≫ q.hom) ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).toTruncated := by
  have hH : (k ≫ initialConeTensorCornerInclusion A L) ≫ H = k ≫ p ≫ q.hom := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    calc
      _ = ((ihom O).obj C.obj).δ 1
          (((pre k).app C.obj).app (Opposite.op ⦋1⦌) a.edge) :=
        (a.map ((pre k).app C.obj)).src_eq.symm
      _ = _ := by rw [hk]; rfl
  obtain ⟨n⟩ := exists_specifiedBoundaryEdgeNormalization
    (initialConeTensorCornerInclusion A L) H (p ≫ q.hom) a ha
  obtain ⟨d⟩ := exists_verdierInitialConeTensorRefinement h A L p n.diagram n.boundary
  obtain ⟨U, hU, hiU⟩ := d.exists_relativeComparison
  have hN : (k ≫ initialConeTensorCornerInclusion A L) ≫ n.diagram = k ≫ p ≫ q.hom := by
    rw [Category.assoc, n.boundary]
  have hD : (k ≫ initialConeTensorCornerInclusion A L) ≫ (d.diagram ≫ q.hom) =
      k ≫ p ≫ q.hom := by
    rw [Category.assoc, ← Category.assoc (initialConeTensorCornerInclusion A L), d.boundary]
  have hUfixed : ((k ≫ initialConeTensorCornerInclusion A L) ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst O Δ[1] ≫ (k ≫ p ≫ q.hom) := by
    rw [comp_whiskerRight, Category.assoc, hU]
    rfl
  have hNfixed : ((k ≫ initialConeTensorCornerInclusion A L) ▷ (Δ[1] : SSet.{u})) ≫
      n.homotopy.h = fst O Δ[1] ≫ (k ≫ p ≫ q.hom) := by
    rw [comp_whiskerRight, Category.assoc, n.homotopy_restriction]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.simplicialHomotopyOfFunctorEdge_pre_eq_constant k (k ≫ p ≫ q.hom)
      a.toTruncated hk
  have hiN : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge n.homotopy x).toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible n.edge.toTruncated n.isInvertible
  obtain ⟨eU⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedDiagramVertexIso_of_relativeHomotopy
    (k ≫ initialConeTensorCornerInclusion A L) (k ≫ p ≫ q.hom)
    (d.diagram ≫ q.hom) n.diagram hD hN U hUfixed hiU
  obtain ⟨eN⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedDiagramVertexIso_of_relativeHomotopy
    (k ≫ initialConeTensorCornerInclusion A L) (k ≫ p ≫ q.hom)
    H n.diagram hH hN n.homotopy hNfixed hiN
  obtain ⟨J, hJ, hiJ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relative_homotopy_of_fixedDiagram_vertexIso
    (k ≫ initialConeTensorCornerInclusion A L) (k ≫ p ≫ q.hom)
    (d.diagram ≫ q.hom) H hD hH (eU ≪≫ eN.symm)
  exact ⟨d.diagram, J, d.boundary, hJ, hiJ⟩

end SerrePositivity.KST.LocalizingInvariants
