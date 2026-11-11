module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerProjectionLaws

/-!
# 元の corner 比較の正規化された Over 射影

概要：実 corner 比較を同じ Over n に射影すると元の次数モデルの第二射影になる。
方針：次数正規化の射影式を逆に解き、元の corner の第一射影を計算する。
規約：元の指定点・全単体・同じ次数同型を保つ。
使われ方：実評価の左脚を元の comma の評価自然変換へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

lemma roofQuillenDegreeNormalizationMap_inv_over :
    inv (roofQuillenDegreeNormalizationMap A Y q b f) ≫
      pullback.fst _ _ ≫ (roofTargetDegreeSliceIso A Y q b).hom = pullback.snd _ _ := by
  rw [IsIso.inv_comp_eq]
  exact (roofQuillenDegreeNormalizationMap_over A Y q b f).symm

lemma roofQuillenDegreeCornerMap_normalizedOver :
    roofQuillenDegreeCornerMap A Y q b f ≫ roofCornerNormalizationMap A Y q b ≫
      roofCornerNormalizedProjection A Y q b = pullback.snd _ _ := by
  rw [roofQuillenDegreeCornerMap, Category.assoc, roofCornerNormalizationMap_over,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCornerBase _ _ _), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCornerBase_fst]
  exact roofQuillenDegreeNormalizationMap_inv_over A Y q b f

end SerrePositivity.EInfinity.FrameHom.FrameArrows
