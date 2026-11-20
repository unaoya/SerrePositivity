module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # Cubical 合成の三生成射の tensor 計算
概要：両生成射の合成の回収式から、三生成射の左右の合成を計算する。
方針：モノイダル圏の tensor と合成の交換則を使う。
規約：因子の順序を保つ。使われ方：元の necklace 合成の結合則。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- 左から二つずつ合成する三生成射の回収式。 -/
lemma cubicalComposeTensor_left {A B C P Q R S T E F : D}
    (a : A ⟶ P) (b : B ⟶ Q) (c : C ⟶ R)
    (s : P ⊗ Q ⟶ S) (t : S ⊗ R ⟶ T)
    (m : A ⊗ B ⟶ E) (e : E ⟶ S) (n : E ⊗ C ⟶ F) (f : F ⟶ T)
    (hs : (a ⊗ₘ b) ≫ s = m ≫ e) (ht : (e ⊗ₘ c) ≫ t = n ≫ f) :
    ((a ⊗ₘ b) ⊗ₘ c) ≫ s ▷ R ≫ t = m ▷ C ≫ n ≫ f := by
  rw [← Category.assoc, tensorHom_comp_whiskerRight, hs,
    ← whiskerRight_comp_tensorHom, Category.assoc, ht]

/-- 右から二つずつ合成する三生成射の回収式。 -/
lemma cubicalComposeTensor_right {A B C P Q R S T E F : D}
    (a : A ⟶ P) (b : B ⟶ Q) (c : C ⟶ R)
    (s : Q ⊗ R ⟶ S) (t : P ⊗ S ⟶ T)
    (m : B ⊗ C ⟶ E) (e : E ⟶ S) (n : A ⊗ E ⟶ F) (f : F ⟶ T)
    (hs : (b ⊗ₘ c) ≫ s = m ≫ e) (ht : (a ⊗ₘ e) ≫ t = n ≫ f) :
    (a ⊗ₘ (b ⊗ₘ c)) ≫ P ◁ s ≫ t = A ◁ m ≫ n ≫ f := by
  rw [← Category.assoc, tensorHom_comp_whiskerLeft, hs,
    ← whiskerLeft_comp_tensorHom, Category.assoc, ht]

omit [MonoidalCategory D] in
/-- 三つの合成の等号を、同じ後合成を持つ右結合の式へ移す。 -/
lemma cubicalComposeTensor_postcompose_eq {A B C X E F G : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ X)
    (d : A ⟶ E) (e : E ⟶ F) (f : F ⟶ X) (g : X ⟶ G)
    (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    a ≫ b ≫ c ≫ g = d ≫ e ≫ f ≫ g := by
  simpa only [Category.assoc] using congrArg (fun k => k ≫ g) h

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
