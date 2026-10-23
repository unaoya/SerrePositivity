module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftIntervalComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantSimplex

/-!
概要：元の左 Hom 区間の実際の単体を、weighted cone の時間切断として表示する。
方針：既存の左区間の切断公式と一定図式の cone の厳密な表示を合成する。
規約：coherent 単体そのものを比較し、頂点での一致に弱めない。
使われ方：weighted prism の正頂点間の Hom を元の左区間の作用へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 左区間の全単体は、元の一定 weighted cone の同じ時間切断への制限。 -/
lemma coherentLeftHomInterval_weightedConstantCone (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s)) =
    (SimplicialNerve C).map
      (SimplexCategory.mkHom (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
      (weightedConeSimplex F x
        (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s)) := by
  rw [coherentLeftHomInterval_evaluate, weightedConstantConeSimplex_eq]
  rfl

/-- 同じ単体の時刻零の正頂点は、元の始点に厳密に一致。 -/
lemma coherentLeftHomInterval_obj_zero (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (k : Fin (n + 1))
    (hk : (stdSimplex.objEquiv t).toOrderHom k = 0) :
    ((coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))).obj
        ⟨ULift.up k⟩ = x := by
  rw [coherentLeftHomInterval_weightedConstantCone]
  change Fin.cases x (fun _ => F.obj i)
    (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom k) = x
  rw [show coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom k = 0 from ite_eq_left hk]
  rfl

/-- 同じ単体の時刻一の正頂点は、元の終点に厳密に一致。 -/
lemma coherentLeftHomInterval_obj_one (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (k : Fin (n + 1))
    (hk : (stdSimplex.objEquiv t).toOrderHom k = 1) :
    ((coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))).obj
        ⟨ULift.up k⟩ = F.obj i := by
  rw [coherentLeftHomInterval_weightedConstantCone]
  change Fin.cases x (fun _ => F.obj i)
    (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom k) = F.obj i
  rw [show coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom k = k.succ from
    ite_eq_right (by rw [hk]; decide)]
  rfl

end SerrePositivity.InfinityCategories
