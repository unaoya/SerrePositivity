module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeCylinderMap

/-!
概要：左に零単体を補った fat 錐の円柱と、元の図式の円柱を厳密に同定する。
方針：補充・忘却の二射を、零単体の各次数の一意性で互いの逆と示す。
規約：充填性は不要。全パラメータで厳密な同型。
使われ方：固定頂点の fat 錐と定値始域からの変換の円柱の照合。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 左の一点を補う射と忘れる射は、元の円柱との厳密な同型をなす。 -/
def fatConeCylinderIso (K : SSet.{u}) :
    ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ K ≅ K ⊗ Δ[1] where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderProjection K
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderEmbedding K
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · apply Prod.ext
      · apply stdSimplex.objEquiv.injective
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro i
        change (_ : Fin 1) = _
        exact Subsingleton.elim _ _
      · rfl
    · rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 元の円柱を、左の一点を持つ fat 錐の円柱へ入れる。 -/
def fatConeCylinderMap (K : SSet.{u}) : K ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[0] K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderEmbedding K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] K

/-- fat 錐の円柱の零端は指定頂点側の包含。 -/
lemma fatConeCylinderMap_zero (K : SSet.{u}) :
    SSet.ι₀ (X := K) ≫ fatConeCylinderMap K =
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K := by
  rw [fatConeCylinderMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderEmbedding_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_zero]

/-- fat 錐の円柱の一端は元の図式の包含。 -/
lemma fatConeCylinderMap_one (K : SSet.{u}) :
    SSet.ι₁ (X := K) ≫ fatConeCylinderMap K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K := by
  rw [fatConeCylinderMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderEmbedding_one,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_one, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
