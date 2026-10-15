module
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! # dg関手のopposite -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory BraidedCategory Opposite
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {F : Type t}
  [DGCategory A D] [DGCategory A E] [DGCategory A F]

/-- Hom chain mapを保ち、両側のKoszul交換をbraidingの自然性で比較する。 -/
def op (G : DGFunctor A D E) : DGFunctor A Dᵒᵖ Eᵒᵖ where
  obj x := Opposite.op (G.obj x.unop)
  map x y := G.map y.unop x.unop
  map_id x := G.map_id x.unop
  map_comp x y z := by
    change (β_ _ _).hom ≫ eComp (Complex A) z.unop y.unop x.unop ≫
      G.map z.unop x.unop = _
    rw [G.map_comp]
    change (β_ _ _).hom ≫ (G.map z.unop y.unop ⊗ₘ G.map y.unop x.unop) ≫
      eComp (Complex A) (G.obj z.unop) (G.obj y.unop) (G.obj x.unop) =
      (G.map y.unop x.unop ⊗ₘ G.map z.unop y.unop) ≫ (β_ _ _).hom ≫
        eComp (Complex A) (G.obj z.unop) (G.obj y.unop) (G.obj x.unop)
    exact (braiding_naturality_assoc (G.map y.unop x.unop) (G.map z.unop y.unop)
      (eComp (Complex A) (G.obj z.unop) (G.obj y.unop) (G.obj x.unop))).symm

@[simp]
lemma op_id : (DGFunctor.id (A := A) D).op = DGFunctor.id (A := A) Dᵒᵖ := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (DGFunctor.id (A := A) D).op) (G := DGFunctor.id (A := A) Dᵒᵖ) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

@[simp]
lemma op_comp (G : DGFunctor A D E) (H : DGFunctor A E F) :
    (G.comp H).op = G.op.comp H.op := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (G.comp H).op) (G := G.op.comp H.op) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded.DGFunctor
