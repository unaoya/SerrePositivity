module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellCommonSourcePrimitives
public import SerrePositivity.InfinityCategories.Derived.DGLastHornRefinementFiller

/-! # 実最後外ホーン有限族の一つの追加閉分母後の同時原始元

概要：回収始対象が共通な有限族に、一つの追加実閉分母と全ての残差原始元を供給する。
方針：同じ共通始域へ揃えた有限 cell 残差を同時に消し、元の型付き細分データへ戻す。
規約：各細分の始対象と追加分母の実辺を厳密に共通化する。使われ方：有限図式辺の実充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

/-- 一つの追加実閉分母を持つ実ホーン有限族の原始元データ。 -/
structure DGLastHornFiniteRefinement (P : Set D) (a : D) {m : ℕ}
    (σ : Fin m → ((Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)) where
  q : D
  s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) a
  denominator : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P
  residuals (i : Fin m) : DGLastHornResidualRefinement P (σ i)
  source_eq (i : Fin m) : (residuals i).q = q
  denominator_edge_eq (i : Fin m) :
    (dgClosedEdge A D (residuals i).s).edge = (dgClosedEdge A D s).edge

/-- 各最後辺が実分母で回収始対象が共通なら、一つの追加実閉分母後に全原始元がある。 -/
theorem dgLastHornFiniteRefinement_nonempty [IsDGPretriangulated A D] (P : Set D)
    (a : D) {m : ℕ} (σ : Fin m → ((Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D))
    (hsource : ∀ i, (HornData.knownData (σ i)).obj 0 = a)
    (hW : ∀ i, (dgClosedEdge A D (dgLastHornFinalClosed (σ i))).edge ∈ dgVerdierEdges A D P) :
    Nonempty (DGLastHornFiniteRefinement P a σ) := by
  have hM i := dgYonedaVerdierCone_derivedFiniteCell A D P (dgLastHornFinalClosed (σ i)) (hW i)
  have hf i : differential A (D := RightModule A D)
      (x := representable A ((HornData.knownData (σ i)).obj 0))
      (y := ForgetEnrichment.to (Complex A) (dgLastHornYonedaCone (σ i))) (n := -1)
      (dgLastHornYonedaResidual (σ i)) = 0 := dgLastHornYonedaResidual_closed (σ i)
  obtain ⟨q, s, hs, h⟩ := dgFiniteCellGraded_exists_transportedSource_primitives A D P a
    (fun i => (HornData.knownData (σ i)).obj 0) hsource
    (fun i => dgLastHornYonedaCone (σ i)) hM (fun _ => -1) (fun _ => -2) (fun _ => by decide)
    (fun i => dgLastHornYonedaResidual (σ i)) hf
  choose b db using h
  exact ⟨{
    q := q
    s := s
    denominator := hs
    residuals := fun i => {
      q := q
      s := dgClosedTargetTransport A D s (hsource i).symm
      denominator := dgClosedTargetTransport_mem A D P s (hsource i).symm hs
      primitive := b i
      differential_primitive := db i }
    source_eq := fun _ => rfl
    denominator_edge_eq := fun i => dgClosedTargetTransport_edge A D s (hsource i).symm }⟩

end SerrePositivity.InfinityCategories
