module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-! # The actual right bar leg is detected on its source section

The source section becomes invertible using the already proved left-leg
contraction. Thus testing the right leg reduces to an actual comma section.
-/

@[expose] public section
universe v uD vD uB vB vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

lemma spanSection_right (d : D) : spanSection p F d ≫ (spanRight p F).app d =
    commaSection p F (𝟙 (p.obj d)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  let A := (Functor.const (Fin (n.unop.len + 1))).obj (identityPoint F d n x.down) ⋙
    CostructuredArrow.post (Functor.Elements.π (F.flip.obj n)) p d
  let B := (Functor.const (Fin (n.unop.len + 1))).obj
    (sectionPoint p F (𝟙 (p.obj d)) n x.down)
  change A = B
  have hobj (i : Fin (n.unop.len + 1)) : A.obj i = B.obj i :=
    congrArg (fun k => sectionPoint p F k n x.down) (p.map_id d)
  apply CategoryTheory.Functor.hext hobj
  intro i j f
  apply elementComma_hom_heq p F (hobj i) (hobj j)
  rfl

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max uD vD v vB} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma spanSection_image_isIso (d : D) : IsIso (L.map (spanSection p F d)) := by
  have : IsIso (L.map ((spanLeft p F).app d)) :=
    inferInstanceAs (IsIso (spanLeftImageIso p F L hL d).hom)
  apply (isIso_comp_right_iff (L.map (spanSection p F d))
    (L.map ((spanLeft p F).app d))).mp
  rw [← L.map_comp, spanSection_retract, L.map_id]
  infer_instance

include hL in
lemma spanRight_isIso_iff_section (d : D) : IsIso (L.map ((spanRight p F).app d)) ↔
    IsIso (L.map (commaSection p F (𝟙 (p.obj d)))) := by
  have := spanSection_image_isIso p F L hL d
  rw [← spanSection_right, L.map_comp]
  exact (isIso_comp_left_iff _ _).symm

end SerrePositivity.SimplicialModel.BarConstruction
