module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-! # Gluing whole cotensor families on an actual pushout square -/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel.BoundaryCotensor

namespace SerrePositivity.SimplicialModel.PushoutCotensor
variable {A B C Q T P : SSet.{w}} {u : A ⟶ B} {v : A ⟶ C} {l : B ⟶ Q} {r : C ⟶ Q}
  (sq : IsPushout u v l r) (b : T ⟶ (ihom B).obj P) (c : T ⟶ (ihom C).obj P)
  (h : b ≫ (pre u).app P = c ≫ (pre v).app P)

include h in
lemma transpose_compatible : u ≫ transpose b = v ≫ transpose c := by
  rw [← transpose_restriction, ← transpose_restriction, h]

def glue : T ⟶ (ihom Q).obj P := transpose (sq.desc (transpose b) (transpose c)
  (transpose_compatible b c h))

@[reassoc]
lemma glue_left : glue sq b c h ≫ (pre l).app P = b := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose, sq.inl_desc]

@[reassoc]
lemma glue_right : glue sq b c h ≫ (pre r).app P = c := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose, sq.inr_desc]

include sq in
lemma hom_ext {f g : T ⟶ (ihom Q).obj P}
    (hl : f ≫ (pre l).app P = g ≫ (pre l).app P)
    (hr : f ≫ (pre r).app P = g ≫ (pre r).app P) : f = g := by
  apply transpose_injective
  apply sq.hom_ext
  · rw [← transpose_restriction, ← transpose_restriction, hl]
  · rw [← transpose_restriction, ← transpose_restriction, hr]

end SerrePositivity.SimplicialModel.PushoutCotensor
