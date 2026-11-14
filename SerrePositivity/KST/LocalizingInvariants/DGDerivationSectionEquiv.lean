module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationSection

/-!
概要：実 dg derivation と、分裂平方零代数への射影を切断する実代数射の同値。
方針：切断の第二成分を取り、元の代数射の積保存から Leibniz 則を得る。
規約：厳密な切断の分類。使われ方：導来平方零拡大の模型を作る最初の界面。
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
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)

def Sections := {s : A ⟶ algebra A M // s ≫ projection A M = 𝟙 A}

def derivationOfSection (s : A ⟶ algebra A M) (hs : s ≫ projection A M = 𝟙 A) :
    Derivation A M where
  hom := s.hom ≫ biprod.snd
  unit := by
    rw [← Category.assoc, IsMonHom.one_hom]
    change (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M) ≫ biprod.snd = 0
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one, Category.assoc, biprod.inl_snd, comp_zero]
  leibniz := by
    have hf : s.hom ≫ biprod.fst = 𝟙 A.X := congrArg Mon.Hom.hom hs
    rw [← Category.assoc, IsMonHom.mul_hom, Category.assoc]
    change (s.hom ⊗ₘ s.hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ≫ biprod.snd = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_snd]
    simp only [comp_add, tensorHom_comp_tensorHom_assoc, hf, id_tensorHom, tensorHom_id]

def derivationSectionEquiv : Derivation A M ≃ Sections A M where
  toFun d := ⟨d.section, d.section_projection⟩
  invFun s := derivationOfSection A M s.val s.property
  left_inv d := by
    apply Derivation.ext
    exact biprod.lift_snd _ _
  right_inv s := by
    apply Subtype.ext
    apply Mon.Hom.ext
    apply biprod.hom_ext
    · change biprod.lift (𝟙 A.X) (s.val.hom ≫ biprod.snd) ≫ biprod.fst =
        s.val.hom ≫ biprod.fst
      rw [biprod.lift_fst]
      exact (congrArg Mon.Hom.hom s.property).symm
    · exact biprod.lift_snd _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZero
