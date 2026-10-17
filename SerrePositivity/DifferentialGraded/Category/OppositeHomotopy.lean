module
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! # 主ホモトピー圏からopposite dg圏の主ホモトピー圏への反変比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- Mathlibの豊穣opposite比較を主Kの商へ送る。 -/
def closedToOppositeHomotopy : ClosedCategory A D ⥤ (HomotopyCategory A Dᵒᵖ)ᵒᵖ :=
  ((forgetEnrichmentOppositeEquivalence (Complex A) D).inverse ⋙
    toHomotopy A Dᵒᵖ).rightOp

/-- 元のHom複体は同じなので、opposite比較は境界関係を保つ。 -/
lemma closedToOppositeHomotopy_boundary {x y : ClosedCategory A D} {f g : x ⟶ y}
    (h : boundaryRelation A D f g) :
    (closedToOppositeHomotopy A D).map f = (closedToOppositeHomotopy A D).map g := by
  apply Quiver.Hom.unop_inj
  apply (toHomotopy_map_eq_iff A Dᵒᵖ _ _).mpr
  exact h

/-- 主K(D)のoppositeから主K(Dᵒᵖ)への関手。smallnessは仮定しない。 -/
def homotopyOppositeFunctor : (HomotopyCategory A D)ᵒᵖ ⥤ HomotopyCategory A Dᵒᵖ :=
  (CategoryTheory.Quotient.lift (boundaryRelation A D) (closedToOppositeHomotopy A D)
    (fun _ _ _ _ h => closedToOppositeHomotopy_boundary A D h)).leftOp

end SerrePositivity.DifferentialGraded
