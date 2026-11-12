module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyFatCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTransform
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison

/-!
概要：元の図式の円柱を、同じ図式を右因子とする錐の join へ写す。
方針：左の零単体を補って fat join の円柱へ入れ、通常の join へ比較する。
規約：円柱の零端と一端は指定頂点側と元の図式側に厳密に一致する。
使われ方：錐の全パラメータを定値始域からの変換へ移す。

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

/-- 元の円柱に左の一点を補い、fat 錐の円柱へ入れる。 -/
def fatConeCylinderEmbedding (K : SSet.{u}) :
    K ⊗ (Δ[1] : SSet.{u}) ⟶ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ K :=
  lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (snd K Δ[1])) (fst K Δ[1])

/-- 円柱の零端での一点の補充は、fat join の左端の lift。 -/
lemma fatConeCylinderEmbedding_zero (K : SSet.{u}) :
    SSet.ι₀ (X := K) ≫ fatConeCylinderEmbedding K =
      lift ((SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫ SSet.ι₀)
        (𝟙 K) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 円柱の一端での一点の補充は、fat join の右端の lift。 -/
lemma fatConeCylinderEmbedding_one (K : SSet.{u}) :
    SSet.ι₁ (X := K) ≫ fatConeCylinderEmbedding K =
      lift ((SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫ SSet.ι₁)
        (𝟙 K) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の図式の円柱から、同じ頂点・図式の通常の join 錐へ写す。 -/
def coneCylinderMap (K : SSet.{u}) : K ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K :=
  fatConeCylinderEmbedding K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[0] K

/-- 零端は元の左頂点側の包含を経由する。 -/
lemma coneCylinderMap_zero (K : SSet.{u}) :
    SSet.ι₀ (X := K) ≫ coneCylinderMap K =
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K := by
  rw [coneCylinderMap, ← Category.assoc, fatConeCylinderEmbedding_zero,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_zero, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_comparison]

/-- 一端は同じ元の右図式の包含。 -/
lemma coneCylinderMap_one (K : SSet.{u}) :
    SSet.ι₁ (X := K) ≫ coneCylinderMap K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K := by
  rw [coneCylinderMap, ← Category.assoc, fatConeCylinderEmbedding_one,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_one, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
