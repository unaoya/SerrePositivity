module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! 全 Hom の鎖同型に沿う dg 圏構造の移送。単位と合成を共役し、三つの圏法則を証明する。 -/
@[expose] public section
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) (D : Type w) [DGCategory R D]
  (f : C → D) (H : C → C → Complex R) (e : ∀ x y, H x y ≅ homObject R D (f x) (f y))
/-- 元の閉単位を指定 Hom へ移す。 -/
def dgGluingHomTransportUnit (x : C) : 𝟙_ (Complex R) ⟶ H x x :=
  eId (Complex R) (f x) ≫ (e x x).inv
/-- 実豊穣合成を全 Hom の鎖同型で共役する。 -/
def dgGluingHomTransportComp (x y z : C) : H x y ⊗ H y z ⟶ H x z :=
  ((e x y).hom ⊗ₘ (e y z).hom) ≫ eComp (Complex R) (f x) (f y) (f z) ≫ (e x z).inv
lemma dgGluingHomTransport_id_comp (x y : C) :
    (λ_ (H x y)).inv ≫ dgGluingHomTransportUnit R C D f H e x ▷ _ ≫
      dgGluingHomTransportComp R C D f H e x x y = 𝟙 _ := by
  apply (cancel_mono (e x y).hom).1
  simp only [dgGluingHomTransportUnit, dgGluingHomTransportComp, comp_whiskerRight, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, whiskerRight_comp_tensorHom_assoc,
    Category.id_comp,
    leftUnitor_inv_comp_tensorHom_assoc, e_id_comp]
lemma dgGluingHomTransport_comp_id (x y : C) :
    (ρ_ (H x y)).inv ≫ _ ◁ dgGluingHomTransportUnit R C D f H e y ≫
      dgGluingHomTransportComp R C D f H e x y y = 𝟙 _ := by
  apply (cancel_mono (e x y).hom).1
  simp only [dgGluingHomTransportUnit, dgGluingHomTransportComp, whiskerLeft_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp_tensorHom_assoc,
    Category.id_comp, rightUnitor_inv_comp_tensorHom_assoc, e_comp_id]
lemma dgGluingHomTransport_assoc (w x y z : C) :
    (α_ _ _ _).inv ≫ dgGluingHomTransportComp R C D f H e w x y ▷ _ ≫
      dgGluingHomTransportComp R C D f H e w y z =
    _ ◁ dgGluingHomTransportComp R C D f H e x y z ≫
      dgGluingHomTransportComp R C D f H e w x z := by
  apply (cancel_mono (e w z).hom).1
  simp only [dgGluingHomTransportComp, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, whiskerRight_comp_tensorHom_assoc,
    whiskerLeft_comp_tensorHom_assoc]
  rw [← tensorHom_comp_whiskerRight_assoc, ← tensorHom_comp_whiskerLeft_assoc,
    ← associator_inv_naturality_assoc, e_assoc]

/-- 指定された全 Hom 鎖同型で、実 dg 圏構造を移す。 -/
@[instance_reducible]
def dgGluingHomIsoEnrichment : DGCategory R C :=
  ofHomObjects R C H (dgGluingHomTransportUnit R C D f H e)
    (dgGluingHomTransportComp R C D f H e)
    (dgGluingHomTransport_id_comp R C D f H e)
    (dgGluingHomTransport_comp_id R C D f H e)
    (dgGluingHomTransport_assoc R C D f H e)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
