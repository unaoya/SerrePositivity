module
public import SerrePositivity.InfinityCategories.Stable.SimplicialHomotopyOpposite
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeFunctor
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
/-!
概要：実 dg nerve 関手の全ホモトピーを、反対 dg 圏の元の実関手へ戻す。
方針：実区間の反転と dg nerve の反対比較の厳密自然性を合成する。
規約：同じ実両端を回収する。使われ方：普遍余単位の比較 cochain の方向反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C E : Type v) [DGCategory R C] [DGCategory R E]
/-- 同じ実全関手ホモトピーを、反対 dg nerve の実両端へ移す。 -/
def dgNerveOppositeHomotopy (F G : DGFunctor R C E)
    (H : SSet.Homotopy (dgNerve.map F) (dgNerve.map G)) :
    SSet.Homotopy (dgNerve.map G.op) (dgNerve.map F.op) := by
  let eC := dgNerveOppositeIso R C
  let eE := dgNerveOppositeIso R E
  let H' := functorHomotopyPrecomp
    (functorHomotopyPostcomp (SerrePositivity.InfinityCategories.homotopyOpposite H) eE.hom) eC.inv
  refine { h := H'.h, h₀ := H'.h₀.trans ?_, h₁ := H'.h₁.trans ?_, rel := H'.rel }
  · change (dgNerveOppositeIso R C).inv ≫ opFunctor.map (dgNerve.map G) ≫
      (dgNerveOppositeIso R E).hom = dgNerve.map G.op
    rw [dgNerveOppositeIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · change (dgNerveOppositeIso R C).inv ≫ opFunctor.map (dgNerve.map F) ≫
      (dgNerveOppositeIso R E).hom = dgNerve.map F.op
    rw [dgNerveOppositeIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
end SerrePositivity.InfinityCategories
