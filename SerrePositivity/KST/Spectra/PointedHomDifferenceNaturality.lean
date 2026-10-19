module

public import SerrePositivity.KST.Spectra.FundamentalLoopNaturality

/-!
概要：元の二つの同じ始点からの経路の差は、点つき射と基点の移送に自然。
方針：辺の一単体の等式から始点の等式を回収し、ホモトピー圏の関手で差を写す。
規約：元の辺を保持。使われ方：比較正方形の右辺の差を元の apex 射の作用へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.FundamentalLoop

/-- 元の端点の厳密な変更は、同じホモトピー圏の辺の類の共役表示に等しい。 -/
lemma homMk_ofEq {X : SSet.{u}} {a b c d : X _⦋0⦌} (e : X.Edge a b)
    (ha : a = c) (hb : b = d) :
    SSet.HomotopyCategory.homMk (e.ofEq ha hb) =
      eqToHom (congrArg (SSet.HomotopyCategory.mk (X := X)) ha).symm ≫
        SSet.HomotopyCategory.homMk e ≫
        eqToHom (congrArg (SSet.HomotopyCategory.mk (X := X)) hb) := by
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 元の二つの辺の差の像は、同じ始点・基点の像に表示した二つの元の像の差。 -/
lemma pointedHomMap_difference {P Q : PointedSimplicialSet.{u}}
    (p : P ⟶ Q) {a : P.right _⦋0⦌} {b : Q.right _⦋0⦌}
    (e f : P.right.Edge a P.basepoint) (e' f' : Q.right.Edge b Q.basepoint)
    (he : p.right.app (Opposite.op ⦋1⦌) e.edge = e'.edge)
    (hf : p.right.app (Opposite.op ⦋1⦌) f.edge = f'.edge)
    [IsIso (SSet.HomotopyCategory.homMk e)] [IsIso (SSet.HomotopyCategory.homMk e')] :
    pointedHomMap p (inv (SSet.HomotopyCategory.homMk e) ≫
      SSet.HomotopyCategory.homMk f) =
    inv (SSet.HomotopyCategory.homMk e') ≫ SSet.HomotopyCategory.homMk f' := by
  have ha : p.right.app (Opposite.op ⦋0⦌) a = b :=
    (e.map p.right).src_eq.symm.trans
      ((congrArg (fun s ↦ Q.right.δ 1 s) he).trans e'.src_eq)
  have hb := PointedSimplicialSet.hom_basepointAt p (Opposite.op ⦋0⦌)
  have he' : e' = (e.map p.right).ofEq ha hb := SSet.Edge.ext he.symm
  have hf' : f' = (f.map p.right).ofEq ha hb := SSet.Edge.ext hf.symm
  apply (cancel_epi (SSet.HomotopyCategory.homMk e')).mp
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [he', hf', homMk_ofEq, homMk_ofEq]
  unfold pointedHomMap
  rw [Functor.map_comp, Functor.map_inv]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change _ ≫ (hoFunctor.map p.right).toFunctor.map (SSet.HomotopyCategory.homMk e) ≫
    inv ((hoFunctor.map p.right).toFunctor.map (SSet.HomotopyCategory.homMk e)) ≫ _ = _
  simp only [IsIso.hom_inv_id_assoc]
  rfl

end SerrePositivity.KST.Spectra.FundamentalLoop
