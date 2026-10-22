module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionSquareMap
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionIdentity

/-!
概要：底の厳密な三角形上の制限射と、底が変わる二つの双加群射の合成を構成する。
方針：既存の実正方形射を恒等制限同型で戻す。
規約：underlying 射は元の射・合成そのもの。使われ方：共通零底上の係数逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D : Mon C} (f : A ⟶ B) (d : A ⟶ D) (t : B ⟶ D) (h : f ≫ t = d)
  {M : Bimod B B} {N : Bimod D D} (m : M ⟶ bimoduleRestrict t N)

def bimoduleRestrictOver : bimoduleRestrict f M ⟶ bimoduleRestrict d N :=
  bimoduleRestrictSquareMap f d (𝟙 A) t (h.trans (Category.id_comp d).symm) m ≫
    (bimoduleRestrictionIdIso (bimoduleRestrict d N)).hom

lemma bimoduleRestrictOver_hom : (bimoduleRestrictOver f d t h m).hom = m.hom := by
  change m.hom ≫ 𝟙 N.X = m.hom
  exact Category.comp_id _

variable {L : Bimod A A} (l : L ⟶ bimoduleRestrict f M)

def bimoduleMapOverComp : L ⟶ bimoduleRestrict (f ≫ t) N :=
  l ≫ bimoduleRestrictOver f (f ≫ t) t rfl m

lemma bimoduleMapOverComp_hom : (bimoduleMapOverComp f t m l).hom = l.hom ≫ m.hom := by
  change l.hom ≫ (bimoduleRestrictOver f (f ≫ t) t rfl m).hom = l.hom ≫ m.hom
  rw [bimoduleRestrictOver_hom]

def bimoduleRestrictionMap {A B : Mon C} (f : A ⟶ B) {M N : Bimod B B} (m : M ⟶ N) :
    bimoduleRestrict f M ⟶ bimoduleRestrict f N where
  hom := m.hom
  left_act_hom := by
    change ((f.hom ▷ M.X) ≫ M.actLeft) ≫ m.hom =
      (A.X ◁ m.hom) ≫ (f.hom ▷ N.X) ≫ N.actLeft
    rw [Category.assoc, m.left_act_hom]
    simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id]
  right_act_hom := by
    change ((M.X ◁ f.hom) ≫ M.actRight) ≫ m.hom =
      (m.hom ▷ A.X) ≫ (N.X ◁ f.hom) ≫ N.actRight
    rw [Category.assoc, m.right_act_hom]
    simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id]

lemma bimoduleRestrictionMap_hom {A B : Mon C} (f : A ⟶ B) {M N : Bimod B B} (m : M ⟶ N) :
    (bimoduleRestrictionMap f m).hom = m.hom := rfl

end SerrePositivity.KST.LocalizingInvariants
