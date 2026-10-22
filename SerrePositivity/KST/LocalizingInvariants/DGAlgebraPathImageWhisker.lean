module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapLaws

/-!
概要：経路の係数表示の等式を、源の前合成と係数射の追加後合成を保って移す。
方針：経路関手の合成保存と圏の結合則だけを使う。
規約：全経路の等式を要求する。使われ方：具体的な Γ の ImageWitness 表示の移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B C P Q T : Mon (Complex R)}

lemma map_image_whisker (e : T ⟶ P) (v : P ⟶ algebra R A) (s : P ⟶ Q)
    (w : Q ⟶ algebra R B) (f : A ⟶ B) (g : B ⟶ C)
    (h : v ≫ map R f = s ≫ w) :
    e ≫ (v ≫ map R (f ≫ g)) = (e ≫ s) ≫ w ≫ map R g := by
  rw [map_comp, ← Category.assoc v, h]
  simp only [Category.assoc]

lemma map_post_whisker (e : T ⟶ P) (v : P ⟶ algebra R A) (f : A ⟶ B) (g : B ⟶ C) :
    (e ≫ (v ≫ map R f)) ≫ map R g = e ≫ (v ≫ map R (f ≫ g)) := by
  rw [map_comp]
  simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
