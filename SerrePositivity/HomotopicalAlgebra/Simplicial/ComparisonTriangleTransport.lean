module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceMaps

/-! # Strict transport of whole comparison triangle spaces along maps of their two edges -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonTriangleTransport
open KanComparisonTriangle
variable {T K T' K' T'' K'' : SSet.{v}}
  {f g z : T ⟶ K} {f' g' z' : T' ⟶ K'} {f'' g'' z'' : T'' ⟶ K''}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)
  (F' : SSet.Homotopy f' z') (G' : SSet.Homotopy g' z')
  (q : (ihom T).obj K ⟶ (ihom T').obj K')
  (hF : curry F.h ≫ q = curry F'.h) (hG : curry G.h ≫ q = curry G'.h)

include hF hG in
lemma hornMap_post : hornMap F G ≫ q = hornMap F' G' := by
  apply SSet.horn.hom_ext'
  intro i hi
  rw [← Category.assoc]
  fin_cases i
  · exact (congrArg (fun a => a ≫ q) (hornMap_zero F G)).trans
      (hG.trans (hornMap_zero F' G').symm)
  · exact (congrArg (fun a => a ≫ q) (hornMap_one F G)).trans
      (hF.trans (hornMap_one F' G').symm)
  · exact (hi rfl).elim

def map : ComparisonTriangleChoices.obj F G ⟶ ComparisonTriangleChoices.obj F' G' :=
  RelativeChoiceSpace.postMap (SSet.horn 2 2).ι _ _ q (hornMap_post F G F' G' q hF hG)

def data (d : Data F G) : Data F' G' where
  triangle := d.triangle ≫ q
  face_zero := by rw [← Category.assoc, d.face_zero, hG]
  face_one := by rw [← Category.assoc, d.face_one, hF]

lemma ofData_map (d : Data F G) : ComparisonTriangleChoices.ofData F G d ≫
    map F G F' G' q hF hG = ComparisonTriangleChoices.ofData F' G' (data F G F' G' q hF hG d) :=
  RelativeChoiceSpace.postMap_ofExtension _ _ _ _ _ _ _

lemma family_map {L : SSet.{v}} (c : L ⟶ ComparisonTriangleChoices.obj F G) :
    ComparisonTriangleChoices.family F' G' (c ≫ map F G F' G' q hF hG) =
      ComparisonTriangleChoices.family F G c ≫ q :=
  RelativeChoiceSpace.family_postMap _ _ _ _ _ _

lemma map_id : map F G F G (𝟙 _) (Category.comp_id _) (Category.comp_id _) = 𝟙 _ :=
  RelativeChoiceSpace.postMap_identity _ _

variable (F'' : SSet.Homotopy f'' z'') (G'' : SSet.Homotopy g'' z'')
  (r : (ihom T').obj K' ⟶ (ihom T'').obj K'')
  (hF' : curry F'.h ≫ r = curry F''.h) (hG' : curry G'.h ≫ r = curry G''.h)

lemma map_comp : map F G F' G' q hF hG ≫ map F' G' F'' G'' r hF' hG' =
    map F G F'' G'' (q ≫ r)
      (by rw [← Category.assoc, hF, hF']) (by rw [← Category.assoc, hG, hG']) :=
  RelativeChoiceSpace.postMap_compose _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.ComparisonTriangleTransport
