module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGFiniteCellCommonSourcePrimitives
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornGeneralRefinedCochains

/-! # 任意次元の最後外ホーン有限族の共通原始元

概要：次元が異なってよい有限ホーン族に、一つの追加実閉分母と全残差原始元を供給する。
方針：共通始対象へ揃えた有限 cell 残差を、それぞれの整数次数で同時に消す。
規約：追加始対象と実分母辺を厳密に共通化。使われ方：高次有限図式の同時充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 任意次元の実ホーン有限族に対する、一つの追加分母後の原始元データ。 -/
structure DGGeneralLastHornFiniteRefinement (P : Set D) (a : D) {m : ℕ} {d : Fin m → ℕ}
    (σ : ∀ i, (Λ[d i + 2, Fin.last (d i + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) where
  q : D
  s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) a
  denominator : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  residuals (i : Fin m) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornResidualRefinement P (σ i)
  source_eq (i : Fin m) : (residuals i).q = q
  denominator_edge_eq (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (residuals i).s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge

/-- 共通始対象と実最後分母を持つ有限族の残差は、一つの追加実分母で同時に消せる。 -/
theorem dgGeneralLastHornFiniteRefinement_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D)
    (a : D) {m : ℕ} {d : Fin m → ℕ}
    (σ : ∀ i, (Λ[d i + 2, Fin.last (d i + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hsource : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0 = a)
    (hW : ∀ i, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed (σ i))).edge ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) : Nonempty (DGGeneralLastHornFiniteRefinement P a σ) := by
  have hM i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaVerdierCone_derivedFiniteCell A D P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed (σ i)) (hW i)
  have hf i : _root_.SerrePositivity.DifferentialGraded.differential A (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D)
      (x := representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0))
      (y := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone (σ i))) (n := -(d i : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual (σ i)) = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual_closed (σ i)
  obtain ⟨q, s, hs, h⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteCellGraded_exists_transportedSource_primitives A D P a
    (fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0) hsource
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaCone (σ i)) hM (fun i => -(d i : ℤ))
    (fun i => -(d i : ℤ) - 1) (fun _ => by omega)
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornYonedaResidual (σ i)) hf
  choose b db using h
  exact ⟨{
    q := q
    s := s
    denominator := hs
    residuals := fun i => {
      q := q
      s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (hsource i).symm
      denominator := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s (hsource i).symm hs
      primitive := b i
      differential_primitive := db i }
    source_eq := fun _ => rfl
    denominator_edge_eq := fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s (hsource i).symm }⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
