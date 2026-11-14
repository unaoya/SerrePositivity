module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroSeparatedHom
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：次数が分離した平方零代数射の係数成分は、元の底成分上の実双加群射である。
方針：元の乗法保存を二つの混合積へ制限し、元の係数射影で回収する。
規約：作用保存を入力しない。使われ方：平方零代数の pro 逆からの作用保存逆の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.SeparatedHom
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)}
  (M : Bimod A A) (N : Bimod B B) (r : algebra A M ⟶ algebra B N)
  (d : ℤ) (hd : d < 0) [A.X.IsStrictlyGE 0] [B.X.IsStrictlyGE 0]
  [M.X.IsStrictlyLE d] [N.X.IsStrictlyLE d]

include hd in
lemma coefficient_left : M.actLeft ≫ coefficient M N r =
    ((base M N r).hom ⊗ₘ coefficient M N r) ≫ N.actLeft := by
  have h := IsMonHom.mul_hom r.hom
  change _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ r.hom = (r.hom ⊗ₘ r.hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul B N at h
  rw [hom_diagonal M N r d hd] at h
  have hl := congrArg (fun t =>
    (((biprod.inl : A.X ⟶ (algebra A M).X) ⊗ₘ
      (biprod.inr : M.X ⟶ (algebra A M).X)) ≫ t) ≫
        (biprod.snd : (algebra B N).X ⟶ N.X)) h
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr] at hl
  rw [tensorHom_comp_tensorHom, biprod.inl_map, biprod.inr_map,
    ← tensorHom_comp_tensorHom] at hl
  simpa only [Category.assoc, biprod.inr_map_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr_assoc, biprod.inr_snd,
    Category.comp_id] using hl

include hd in
lemma coefficient_right : M.actRight ≫ coefficient M N r =
    (coefficient M N r ⊗ₘ (base M N r).hom) ≫ N.actRight := by
  have h := IsMonHom.mul_hom r.hom
  change _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ r.hom = (r.hom ⊗ₘ r.hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul B N at h
  rw [hom_diagonal M N r d hd] at h
  have hl := congrArg (fun t =>
    (((biprod.inr : M.X ⟶ (algebra A M).X) ⊗ₘ
      (biprod.inl : A.X ⟶ (algebra A M).X)) ≫ t) ≫
        (biprod.snd : (algebra B N).X ⟶ N.X)) h
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl] at hl
  rw [tensorHom_comp_tensorHom, biprod.inr_map, biprod.inl_map,
    ← tensorHom_comp_tensorHom] at hl
  simpa only [Category.assoc, biprod.inr_map_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl_assoc, biprod.inr_snd,
    Category.comp_id] using hl

def coefficientBimoduleMap : M ⟶ bimoduleRestrict (base M N r) N where
  hom := coefficient M N r
  left_act_hom := by
    change M.actLeft ≫ coefficient M N r =
      (A.X ◁ coefficient M N r) ≫ ((base M N r).hom ▷ N.X) ≫ N.actLeft
    rw [← tensorHom_def'_assoc]
    exact coefficient_left M N r d hd
  right_act_hom := by
    change M.actRight ≫ coefficient M N r =
      (coefficient M N r ▷ A.X) ≫ (N.X ◁ (base M N r).hom) ≫ N.actRight
    rw [← tensorHom_def_assoc]
    exact coefficient_right M N r d hd

end SerrePositivity.KST.LocalizingInvariants.SquareZero.SeparatedHom
