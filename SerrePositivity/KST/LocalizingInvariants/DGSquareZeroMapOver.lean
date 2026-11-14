module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：底の代数射とその上の双加群射が、実平方零代数の射を誘導する。
方針：直和の対角射の単位・積保存を、元の代数射と二つの作用保存へ帰着する。
規約：底も係数も実 chain map。使われ方：Postnikov class の底変更と係数比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Preadditive
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B)
  (M : Bimod A A) (N : Bimod B B) (f : M ⟶ bimoduleRestrict q N)

def mapOver : algebra A M ⟶ algebra B N := by
  let t : M.X ⟶ N.X := f.hom
  have hl : M.actLeft ≫ t = (q.hom ⊗ₘ t) ≫ N.actLeft := by
    change M.actLeft ≫ f.hom = (q.hom ⊗ₘ f.hom) ≫ N.actLeft
    rw [tensorHom_def', Category.assoc]
    exact f.left_act_hom
  have hr : M.actRight ≫ t = (t ⊗ₘ q.hom) ≫ N.actRight := by
    change M.actRight ≫ f.hom = (f.hom ⊗ₘ q.hom) ≫ N.actRight
    rw [tensorHom_def, Category.assoc]
    exact f.right_act_hom
  refine Mon.Hom.mk' (biprod.map q.hom t) ?_ ?_
  · change (η[A.X] ≫ biprod.inl) ≫ biprod.map q.hom t = η[B.X] ≫ biprod.inl
    rw [Category.assoc, biprod.inl_map, ← Category.assoc, IsMonHom.one_hom]
  · change _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ biprod.map q.hom t =
      (biprod.map q.hom t ⊗ₘ biprod.map q.hom t) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul B N
    apply biprodTensor_hom_ext
    all_goals
      simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr, zero_comp,
        tensorHom_comp_tensorHom, biprod.inl_map, biprod.inr_map]
      try simp only [Category.assoc, biprod.inl_map, biprod.inr_map]
      rw [← tensorHom_comp_tensorHom]
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr, comp_zero]
    · simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (biprod.inl : B.X ⟶ (algebra B N).X)) (IsMonHom.mul_hom q.hom)
    · rw [← Category.assoc, hl, Category.assoc]
    · rw [← Category.assoc, hr, Category.assoc]

lemma mapOver_projection : mapOver q M N f ≫ projection B N = projection A M ≫ q := by
  apply Mon.Hom.ext
  exact biprod.map_fst _ _

lemma zeroSection_mapOver : zeroSection A M ≫ mapOver q M N f = q ≫ zeroSection B N := by
  apply Mon.Hom.ext
  exact biprod.inl_map _ _

def negateCoefficient : M ⟶ bimoduleRestrict q N where
  hom := -f.hom
  left_act_hom := by
    change M.actLeft ≫ (-f.hom) = (tensorLeft A.X).map (-f.hom) ≫ _
    rw [Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, f.left_act_hom]
    rfl
  right_act_hom := by
    change M.actRight ≫ (-f.hom) = (tensorRight A.X).map (-f.hom) ≫ _
    rw [Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, f.right_act_hom]
    rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero
