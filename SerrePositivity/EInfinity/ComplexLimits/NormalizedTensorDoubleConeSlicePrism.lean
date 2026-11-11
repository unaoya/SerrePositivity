module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeOverDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：元の大域二重 cone を、恒等錐から同じ slice 図式への全区間 prism に移す。
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
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorDoubleConeSlicePrism : (Δ[1] : SSet.{u + 1}) ⊗
    nerve (normalizedTensorElementIndex A X Y) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (normalizedTensorConePoint A X) :=
  (lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 (Δ[1] : SSet.{u + 1})) ▷
      nerve (normalizedTensorElementIndex A X Y)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorDoubleConeOverJoin A X Y

lemma normalizedTensorDoubleConeSlicePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorDoubleConeSlicePrism A X Y =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)) := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let s : K ⟶ (Δ[0] : SSet.{u + 1}) ⊗ K :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 K)
  let d : (Δ[1] : SSet.{u + 1}) ⟶ (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1])
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (d ▷ K) = s ≫ (SSet.ι₀ (X := Δ[0]) ▷ K) := by rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ ((d ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] K ≫
    normalizedTensorDoubleConeOverJoin A X Y) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (SSet.ι₀ (X := Δ[0]) ▷ K),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero, Category.assoc, normalizedTensorDoubleConeOverJoin_inl]
  rw [← Category.assoc]
  have hs : s ≫ fst Δ[0] K =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := lift_fst _ _
  rw [hs, SSet.const_comp, normalizedTensorIdentityOverPoint_vertex]

lemma normalizedTensorDoubleConeSlicePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve (normalizedTensorElementIndex A X Y)) ≫
      normalizedTensorDoubleConeSlicePrism A X Y = normalizedTensorDoubleConeOverDiagram A X Y := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let s : K ⟶ (Δ[0] : SSet.{u + 1}) ⊗ K :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 K)
  let d : (Δ[1] : SSet.{u + 1}) ⟶ (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] :=
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1])
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (d ▷ K) = s ≫ (SSet.ι₁ (X := Δ[0]) ▷ K) := by rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ ((d ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] K ≫
    normalizedTensorDoubleConeOverJoin A X Y) = _
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (SSet.ι₁ (X := Δ[0]) ▷ K),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one, Category.assoc, normalizedTensorDoubleConeOverJoin_inr]
  rw [← Category.assoc]
  have hs : s ≫ snd Δ[0] K = 𝟙 K := lift_snd _ _
  rw [hs, Category.id_comp]

end SerrePositivity.EInfinity.ComplexLimits
