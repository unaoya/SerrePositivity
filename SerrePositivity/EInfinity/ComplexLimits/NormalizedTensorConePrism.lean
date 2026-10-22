module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeJoin
public import SerrePositivity.InfinityCategories.Core.FatJoinComparison
public import SerrePositivity.InfinityCategories.Core.PrismContraction

/-!
概要：元の大域実 cone を、先端の定値図式から同じ通常 frame 図式への全区間 prism に移す。
方針：同じ join 円柱比較を使い、両端を元の先端と通常図式へ厳密に回収する。
規約：元の全区間族を保持する。使われ方：同じ augmentation・評価との大域三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConePrism : (Δ[1] : SSet.{u + 1}) ⊗
    nerve (normalizedTensorElementIndex A X Y) ⟶ dgNerve A (Complex A) :=
  (lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 (Δ[1] : SSet.{u + 1})) ▷
      nerve (normalizedTensorElementIndex A X Y)) ≫
    joinCylinderMap Δ[0] (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorConeJoin A X Y

lemma normalizedTensorConePrism_zero :
    prismEndpoint 0 (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorConePrism A X Y =
      SSet.const ((dgNerve.vertexEquiv A (Complex A)).symm X) := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let s : K ⟶ (Δ[0] : SSet.{u + 1}) ⊗ K :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 K)
  let d : (Δ[1] : SSet.{u + 1}) ⟶ (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1])
  have he : prismEndpoint 0 K ≫ (d ▷ K) = s ≫ (SSet.ι₀ (X := Δ[0]) ▷ K) := by rfl
  change prismEndpoint 0 K ≫ ((d ▷ K) ≫ joinCylinderMap Δ[0] K ≫
    normalizedTensorConeJoin A X Y) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (SSet.ι₀ (X := Δ[0]) ▷ K),
    joinCylinderMap_zero, Category.assoc, normalizedTensorConeJoin_inl]
  rw [← Category.assoc]
  have hs : s ≫ fst Δ[0] K =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := lift_fst _ _
  rw [hs, SSet.const_comp, normalizedTensorConePoint_vertex]

lemma normalizedTensorConePrism_one :
    prismEndpoint 1 (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorConePrism A X Y = normalizedTensorElementNerveDiagram A X Y := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let s : K ⟶ (Δ[0] : SSet.{u + 1}) ⊗ K :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 K)
  let d : (Δ[1] : SSet.{u + 1}) ⟶ (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1])
  have he : prismEndpoint 1 K ≫ (d ▷ K) = s ≫ (SSet.ι₁ (X := Δ[0]) ▷ K) := by rfl
  change prismEndpoint 1 K ≫ ((d ▷ K) ≫ joinCylinderMap Δ[0] K ≫
    normalizedTensorConeJoin A X Y) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (SSet.ι₁ (X := Δ[0]) ▷ K),
    joinCylinderMap_one, Category.assoc, normalizedTensorConeJoin_inr]
  rw [← Category.assoc]
  have hs : s ≫ snd Δ[0] K = 𝟙 K := lift_snd _ _
  rw [hs, Category.id_comp]

end SerrePositivity.EInfinity.ComplexLimits
