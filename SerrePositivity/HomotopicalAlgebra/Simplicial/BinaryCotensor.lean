module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOneCotensor

/-! # Gluing whole cotensor families on an actual binary coproduct -/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel.BoundaryCotensor

namespace SerrePositivity.SimplicialModel.BinaryCotensor
variable {B C Q T P : SSet.{w}} {l : B ⟶ Q} {r : C ⟶ Q}
  (hQ : IsColimit (BinaryCofan.mk l r)) (b : T ⟶ (ihom B).obj P) (c : T ⟶ (ihom C).obj P)

def glue : T ⟶ (ihom Q).obj P :=
  transpose (hQ.desc (BinaryCofan.mk (transpose b) (transpose c)))

@[reassoc]
lemma glue_left : glue hQ b c ≫ (pre l).app P = b := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose]
  exact hQ.fac (BinaryCofan.mk (transpose b) (transpose c)) ⟨WalkingPair.left⟩

@[reassoc]
lemma glue_right : glue hQ b c ≫ (pre r).app P = c := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose]
  exact hQ.fac (BinaryCofan.mk (transpose b) (transpose c)) ⟨WalkingPair.right⟩

include hQ in
lemma hom_ext {f g : T ⟶ (ihom Q).obj P}
    (hl : f ≫ (pre l).app P = g ≫ (pre l).app P)
    (hr : f ≫ (pre r).app P = g ≫ (pre r).app P) : f = g := by
  apply transpose_injective
  apply hQ.hom_ext
  intro j
  rcases j with ⟨j⟩
  cases j
  · exact (transpose_restriction l f).symm.trans
      ((congrArg transpose hl).trans (transpose_restriction l g))
  · exact (transpose_restriction r f).symm.trans
      ((congrArg transpose hr).trans (transpose_restriction r g))

end SerrePositivity.SimplicialModel.BinaryCotensor
