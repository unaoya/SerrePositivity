module

public import Mathlib.CategoryTheory.Triangulated.Basic

/-!
概要：cone と shift の比較から三角形の同型を束ねる補題。
方針：抽象的な射で三つの可換条件を確認する。
規約：具体的な dg 加群の定義展開を三角形の組立てで繰り返さない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の標準三角形の比較。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：cone の比較と connecting map の可換性から標準三角形の同型を得る。
方針：最初の二対象には恒等同型を使い、第三射の式を shift 同型の逆と合成する。
規約：等しい対象の射の型を隠れた具体的構成へ展開しない。
使われ方：Drinfeld §2.4、KST D4 の代表加群の標準三角形。
-/
def triangleIsoOfComparison {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {P Q R R' S : C} (f : P ⟶ Q) (a : Q ⟶ R) (b : R ⟶ P⟦(1 : ℤ)⟧)
    (a' : Q ⟶ R') (b' : R' ⟶ S) (e : R ≅ R') (s : P⟦(1 : ℤ)⟧ ≅ S)
    (ha : a ≫ e.hom = a') (hb : e.hom ≫ b' = b ≫ s.hom) :
    Triangle.mk f a b ≅ Triangle.mk f a' (b' ≫ s.inv) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    (by simp)
    (by simpa using ha)
    (by
      change b ≫ (𝟙 P)⟦(1 : ℤ)⟧' = e.hom ≫ (b' ≫ s.inv)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, ← Category.assoc, hb,
        Category.assoc, Iso.hom_inv_id, Category.comp_id])

end SerrePositivity.KST.DerivedGeometry
