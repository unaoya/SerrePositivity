module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteCellCommonSourcePrimitives
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornRefinedCochains

/-! # 実四次最後外ホーン有限族の一つの追加閉分母後の同時原始元

概要：回収始対象が共通な有限族に、一つの追加実閉分母と全ての残差原始元を供給する。
方針：同じ共通始域へ揃えた有限 cell 残差を同時に消し、元の型付き細分データへ戻す。
規約：各細分の始対象と追加分母の実辺を厳密に共通化する。使われ方：有限高次図式の実充填。
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

/-- 一つの追加実閉分母を持つ実ホーン有限族の原始元データ。 -/
structure DGFourLastHornFiniteRefinement (P : Set D) (a : D) {m : ℕ}
    (σ : Fin m → ((Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) where
  q : D
  s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) a
  denominator : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  residuals (i : Fin m) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornResidualRefinement P (σ i)
  source_eq (i : Fin m) : (residuals i).q = q
  denominator_edge_eq (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (residuals i).s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge

/-- 各最後辺が実分母で回収始対象が共通なら、一つの追加実閉分母後に全原始元がある。 -/
theorem dgFourLastHornFiniteRefinement_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D)
    (a : D) {m : ℕ} (σ : Fin m → ((Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (hsource : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0 = a)
    (hW : ∀ i, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed (σ i))).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    Nonempty (DGFourLastHornFiniteRefinement P a σ) := by
  have hM i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaVerdierCone_derivedFiniteCell A D P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed (σ i)) (hW i)
  have hf i : _root_.SerrePositivity.DifferentialGraded.differential A (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D)
      (x := representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0))
      (y := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone (σ i))) (n := -2)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual (σ i)) = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual_closed (σ i)
  obtain ⟨q, s, hs, h⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteCellGraded_exists_transportedSource_primitives A D P a
    (fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (σ i)).obj 0) hsource
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaCone (σ i)) hM (fun _ => -2) (fun _ => -3) (fun _ => by decide)
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornYonedaResidual (σ i)) hf
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
