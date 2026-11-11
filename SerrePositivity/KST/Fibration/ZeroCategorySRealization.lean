module
public import SerrePositivity.KST.Fibration.SComponentExactness
public import SerrePositivity.KST.SConstruction.ZeroDirectionsWeak
public import SerrePositivity.KST.SConstruction.BoundaryReduction

/-! # 零入力の全反復 S• 実現と、元の境界商の弱可縮性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 全頂点が零で零対象が存在する実単体集合は、全境界を充填できる。 -/
theorem allZeroVertices_isContractibleKan (X : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (hX : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X := by
  intro n b
  cases n with
  | zero => exact ⟨SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex, boundary.hom_ext₀⟩
  | succ n =>
    let x := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b)
    exact (hX x).2 n b (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- 全ての元の頂点が零なら、任意の有限反復 S の全図式も零。 -/
theorem iteratedSConstruction_allZero (ns : List ℕ) (X : StableModel.{u})
    (hX : ∀ x : X.carrier _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) :
    ∀ v : (iteratedSConstruction ns X.carrier) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v := by
  induction ns with
  | nil => exact hX
  | cons n ns ih =>
    intro v
    apply (sConstruction_isZeroVertex_iff_components _ n v).mpr
    intro a
    exact ih _

/-- 零入力の全多次数の実 core S は可縮 Kan 複体。 -/
theorem multiCoreSConstruction_isContractibleKan_of_allZero (r : ℕ) (X : StableModel.{u})
    (hX : ∀ x : X.carrier _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x)
    (d : Fin r → SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((multiCoreSConstruction r X).obj d) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((multiSConstruction r X).obj d) : SSet.{u})
  rw [multiSConstruction_obj_eq_iterated]
  have hc := allZeroVertices_isContractibleKan _
    (iteratedSConstruction_allZero (List.ofFn (fun i => (d i).unop.len)) X hX)
  let := hc.kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (kanCoreIso _) hc

/-- 同じ多単体的 core 図式から、一点の定値図式への元の自然変換。 -/
def multiCoreSZeroToPoint (r : ℕ) (X : StableModel.{u}) :
    (multiDiagonalDiagramFunctor r).obj X ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u}) where
  app _ := toUnit _
  naturality {_ _} _ := isTerminalTensorUnit.hom_ext _ _

/-- 零入力の同じ全反復実現から一点への実射は anodyne 局所化で可逆。 -/
theorem multiRealization_toPoint_localized_isIso_of_allZero (r : ℕ) (X : StableModel.{u})
    (hX : ∀ x : X.carrier _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit ((multiRealizationFunctor r).obj X))) := by
  apply BisimplicialModel.localized_diagonal_map (multiCoreSZeroToPoint r X)
  intro d
  have hc := multiCoreSConstruction_isContractibleKan_of_allZero r X hX (fun _ => d)
  have := trivialKanFibration_toUnit_of_contractible hc
  exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions)
    (toUnit ((multiCoreSConstruction r X).obj (fun _ => d)))

/-- 零入力の元の境界商から一点への実射も、同じ商比較を用いて可逆。 -/
theorem boundaryReducedRealization_toPoint_localized_isIso_of_allZero
    (r : ℕ) (X : StableModel.{u}) (hX : ∀ x : X.carrier _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (boundaryReducedRealization r X).right)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := boundaryReductionQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r X
  have hm := multiRealization_toPoint_localized_isIso_of_allZero (r + 1) X hX
  have hc : IsIso (Q.map (boundaryReductionQuotient r X) ≫
      Q.map (toUnit (boundaryReducedRealization r X).right)) := by
    rw [← Q.map_comp, comp_toUnit]
    exact hm
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.Fibration
