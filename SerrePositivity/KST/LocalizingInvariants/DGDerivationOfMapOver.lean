module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGDerivationSection

/-!
概要：底の射の上の平方零代数射から、制限した係数への実 derivation を回収する。
方針：元の第二射影を取り、実積保存と底の一致で Leibniz 則を検証する。
規約：底が恒等射でなくても適用できる。使われ方：cell 分解上の Postnikov derivation。
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
  (N : Bimod B B) (s : A ⟶ algebra B N) (hs : s ≫ projection B N = q)

def derivationOfMapOver : Derivation A (bimoduleRestrict q N) where
  hom := s.hom ≫ biprod.snd
  unit := by
    rw [← Category.assoc, IsMonHom.one_hom]
    change _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one B N ≫ biprod.snd = 0
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one, Category.assoc, biprod.inl_snd, comp_zero]
  leibniz := by
    have hf : s.hom ≫ biprod.fst = q.hom := congrArg Mon.Hom.hom hs
    rw [← Category.assoc, IsMonHom.mul_hom, Category.assoc]
    change (s.hom ⊗ₘ s.hom) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul B N ≫ biprod.snd = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_snd, comp_add, ← Category.assoc, ← Category.assoc,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hf]
    change (q.hom ⊗ₘ (s.hom ≫ biprod.snd)) ≫ N.actLeft +
      ((s.hom ≫ biprod.snd) ⊗ₘ q.hom) ≫ N.actRight =
      (A.X ◁ (s.hom ≫ biprod.snd)) ≫ (q.hom ▷ N.X) ≫ N.actLeft +
      ((s.hom ≫ biprod.snd) ▷ A.X) ≫ (N.X ◁ q.hom) ≫ N.actRight
    congr 1
    · rw [tensorHom_def', Category.assoc]
    · rw [tensorHom_def, Category.assoc]

lemma derivationOfMapOver_section : (derivationOfMapOver q N s hs).section ≫
    mapOver q (bimoduleRestrict q N) N (𝟙 (bimoduleRestrict q N)) = s := by
  apply Mon.Hom.ext
  change biprod.lift (𝟙 A.X) (s.hom ≫ biprod.snd) ≫ biprod.map q.hom (𝟙 N.X) = s.hom
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst, Category.id_comp]
    exact (congrArg Mon.Hom.hom hs).symm
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
