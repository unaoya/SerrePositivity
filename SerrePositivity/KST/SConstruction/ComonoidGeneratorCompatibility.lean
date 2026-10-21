module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 生成射上での余モノイド射の法則の判定
概要：余モノイド射である生成射と合成が余モノイド射なら、制限後の二法則を得る。
方針：増大・対角保存を二度使い、tensor 射の合成保存で整理する。
規約：元の余モノイド構造を保持。使われ方：Day 鎖比較の全体への降下。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M X Y : C} [ComonObj M] [ComonObj X] [ComonObj Y]
  (e : M ⟶ X) (f : X ⟶ Y) [IsComonHom e] [IsComonHom (e ≫ f)]

/-- 生成射上で、同じ比較の増大保存を判定する。 -/
lemma comonoidGenerator_counit_compatibility :
    e ≫ (f ≫ ComonObj.counit) = e ≫ ComonObj.counit := by
  rw [← Category.assoc, IsComonHom.hom_counit, IsComonHom.hom_counit]

/-- 生成射上で、同じ比較の対角保存を判定する。 -/
lemma comonoidGenerator_comul_compatibility :
    e ≫ (f ≫ ComonObj.comul) = e ≫ (ComonObj.comul ≫ (f ⊗ₘ f)) := by
  rw [← Category.assoc, IsComonHom.hom_comul, ← Category.assoc,
    IsComonHom.hom_comul, Category.assoc, tensorHom_comp_tensorHom]

end SerrePositivity.KST.SConstruction
