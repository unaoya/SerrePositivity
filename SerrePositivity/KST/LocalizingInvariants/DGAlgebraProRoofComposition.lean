module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProRoof

/-!
概要：構成した二つの実 dg roof の pro 逆を、元の射の合成の逆として合成する。
方針：二段の添字を選び、元の実 pullback と自然性で両三角形を保持する。
規約：同じ span は反転関手より先に選ぶ。使われ方：元の一切断射への roof 抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  {X Y Z : Tower (Mon (Complex R))}

lemma HasSurjectiveRoofProInverse.comp {f : LevelHom X Y} {g : LevelHom Y Z}
    (hf : HasSurjectiveRoofProInverse R (D := D) f)
    (hg : HasSurjectiveRoofProInverse R (D := D) g) :
    HasSurjectiveRoofProInverse R (D := D) (f.comp g) := by
  intro n
  obtain ⟨m, hnm, a, ha⟩ := hf n
  obtain ⟨k, hmk, b, hb⟩ := hg m
  refine ⟨k, hnm.trans hmk, SurjectiveRoof.comp R b a, ?_⟩
  intro L hL
  rw [SurjectiveRoof.comp_value]
  have ha' := (ha L hL).1
  have ah := (ha L hL).2
  have hb' := (hb L hL).1
  have bh := (hb L hL).2
  change L.map (f.app k ≫ g.app k) ≫ _ = _ ∧
    _ ≫ L.map (f.app n ≫ g.app n) = _
  rw [L.map_comp, L.map_comp]
  change (f.map L).app m ≫ SurjectiveRoof.value R L hL a =
    (X.map L).transition hnm at ha'
  change SurjectiveRoof.value R L hL a ≫ (f.map L).app n =
    (Y.map L).transition hnm at ah
  change (g.map L).app k ≫ SurjectiveRoof.value R L hL b =
    (Y.map L).transition hmk at hb'
  change SurjectiveRoof.value R L hL b ≫ (g.map L).app m =
    (Z.map L).transition hmk at bh
  constructor
  · change ((f.map L).app k ≫ (g.map L).app k) ≫
      (SurjectiveRoof.value R L hL b ≫ SurjectiveRoof.value R L hL a) =
        (X.map L).transition _
    rw [Category.assoc, ← Category.assoc ((g.map L).app k), hb',
      ← Category.assoc, ← (f.map L).naturality hmk, Category.assoc, ha',
      (X.map L).transition_comp]
  · change (SurjectiveRoof.value R L hL b ≫ SurjectiveRoof.value R L hL a) ≫
      ((f.map L).app n ≫ (g.map L).app n) = (Z.map L).transition _
    rw [Category.assoc, ← Category.assoc (SurjectiveRoof.value R L hL a), ah,
      (g.map L).naturality hnm, ← Category.assoc, bh, (Z.map L).transition_comp]

lemma hasRoofProInverse_of_proIso {f : LevelHom X Y} (hf : IsProIso f) :
    HasSurjectiveRoofProInverse R (D := D) f := by
  intro i
  obtain ⟨m, hi, a, ha, ah⟩ := hf i
  refine ⟨m, hi, SurjectiveRoof.ofHom R a, ?_⟩
  intro L hL
  rw [SurjectiveRoof.ofHom_value]
  constructor
  · rw [← L.map_comp, ha]
  · rw [← L.map_comp, ah]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
