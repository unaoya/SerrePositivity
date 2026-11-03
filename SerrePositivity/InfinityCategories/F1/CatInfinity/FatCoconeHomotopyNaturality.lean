module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FatJoin
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConstantDiagram
public import SerrePositivity.InfinityCategories.F1.CatInfinity.FatCoconeHomotopy

/-!
概要：太い余錐から定値図式への自然変換を取り出す操作はパラメータに自然。
方針：円柱の並べ替えと直積写像の可換性を curry へ移す。
規約：図式 p を全パラメータで固定する。
使われ方：族の全単射から単体集合の同型を構成するための自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：円柱のパラメータ変更は時間の並べ替えと可換。
方針：三つの座標で計算する。
規約：K と時間の座標は変更しない。使われ方：自然変換の族の自然性。 -/
lemma diagonalCoconeReorder_naturality {A B K : SSet.{u}} (i : B ⟶ A) :
    diagonalCoconeReorder K B ≫ fatJoinCylinderMap (𝟙 K) i =
      (K ◁ (i ▷ (Δ[1] : SSet.{u}))) ≫ diagonalCoconeReorder K A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：太い余錐のパラメータ変更は対応する自然変換の前合成を与える。
方針：fat join の円柱の自然性と curry の自然性を使う。
規約：固定条件の証明の選択は射の等式に影響しない。
使われ方：対角 comma の族の厳密な自然性。 -/
lemma fatCoconeHomotopy_precomp_h {A B K C : SSet.{u}} {p : K ⟶ C}
    (F : fatJoin K A ⟶ C) (hF : fatJoinInl K A ≫ F = p) (i : B ⟶ A)
    (hG : fatJoinInl K B ≫ fatJoinMap (𝟙 K) i ≫ F = p) :
    (fatCoconeHomotopy (fatJoinMap (𝟙 K) i ≫ F) hG).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (fatCoconeHomotopy F hF).h := by
  change curry (diagonalCoconeReorder K B ≫ fatJoinCylinder K B ≫
    fatJoinMap (𝟙 K) i ≫ F) =
      (i ▷ (Δ[1] : SSet.{u})) ≫
        curry (diagonalCoconeReorder K A ≫ fatJoinCylinder K A ≫ F)
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
  rw [← Category.assoc (fatJoinCylinder K B), fatJoinCylinder_map]
  simp only [← Category.assoc]
  rw [diagonalCoconeReorder_naturality]

end SerrePositivity.InfinityCategories.F2
