module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationAdditive
public import SerrePositivity.KST.LocalizingInvariants.DGDerivationOfMapOver

/-!
概要：同じ底を持つ平方零代数への三つの実代数射から、底を保つ s − t + u を構成する。
方針：係数の実 derivation を加減算し、元の底の射の上の代数射へ戻す。
規約：一般の代数射の加算とは区別する。使われ方：実 class 経路の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (s t u : A ⟶ algebra B N) (hs : s ≫ projection B N = q)
  (ht : t ≫ projection B N = q) (hu : u ≫ projection B N = q)

def affineMapOver : A ⟶ algebra B N :=
  (Derivation.add (Derivation.sub (derivationOfMapOver q N s hs)
    (derivationOfMapOver q N t ht)) (derivationOfMapOver q N u hu)).section ≫
      mapOver q (bimoduleRestrict q N) N (𝟙 (bimoduleRestrict q N))

lemma affineMapOver_hom : (affineMapOver q N s t u hs ht hu).hom =
    biprod.lift q.hom (s.hom ≫ biprod.snd - t.hom ≫ biprod.snd + u.hom ≫ biprod.snd) := by
  apply biprod.hom_ext
  · change (biprod.lift (𝟙 A.X) _ ≫ biprod.map q.hom (𝟙 N.X)) ≫ biprod.fst = _
    rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst,
      Category.id_comp, biprod.lift_fst]
  · change (biprod.lift (𝟙 A.X)
      ((s.hom ≫ biprod.snd + -(t.hom ≫ biprod.snd)) + u.hom ≫ biprod.snd) ≫
        biprod.map q.hom (𝟙 N.X)) ≫ biprod.snd = _
    rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
      Category.comp_id, biprod.lift_snd]
    exact congrArg (fun z => z + u.hom ≫ biprod.snd)
      (sub_eq_add_neg (s.hom ≫ biprod.snd) (t.hom ≫ biprod.snd)).symm

lemma affineMapOver_projection : affineMapOver q N s t u hs ht hu ≫ projection B N = q := by
  apply Mon.Hom.ext
  change (affineMapOver q N s t u hs ht hu).hom ≫ biprod.fst = q.hom
  rw [affineMapOver_hom, biprod.lift_fst]

lemma affineMapOver_linear : (affineMapOver q N s t u hs ht hu).hom = s.hom - t.hom + u.hom := by
  rw [affineMapOver_hom]
  apply biprod.hom_ext
  · have hs' : s.hom ≫ biprod.fst = q.hom := congrArg Mon.Hom.hom hs
    have ht' : t.hom ≫ biprod.fst = q.hom := congrArg Mon.Hom.hom ht
    have hu' : u.hom ≫ biprod.fst = q.hom := congrArg Mon.Hom.hom hu
    simp only [biprod.lift_fst, add_comp, sub_comp, hs', ht', hu', sub_self, zero_add]
  · simp only [biprod.lift_snd, add_comp, sub_comp]

lemma affineMapOver_cancel_right : affineMapOver q N s t t hs ht ht = s := by
  apply Mon.Hom.ext
  rw [affineMapOver_linear, sub_add_cancel]

lemma affineMapOver_cancel_left : affineMapOver q N s s u hs hs hu = u := by
  apply Mon.Hom.ext
  rw [affineMapOver_linear, sub_self, zero_add]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
