module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictNativeCocone
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeLeg

/-!
概要：小さい終頂点付加余錐の宇宙移送は、元の指定脚を保つ。
方針：join の一次単体の座標で宇宙同型を評価する。
規約：同じ全一次単体の等式を公開する。
使われ方：拡張ホモロジー余錐と native 余錐の脚の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

lemma dgBarJoinIntervalIdentity :
    SSet.yonedaEquiv (joinStdSimplexIso.{u} 0 0).inv =
      F1B.joinCoconeLegSimplex (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) := by
  apply ((joinStdSimplexIso.{u} 0 0).app (Opposite.op ⦋1⦌)).toEquiv.injective
  simp only [CategoryTheory.Iso.toEquiv_fun]
  erw [← SSet.yonedaEquiv_comp (joinStdSimplexIso.{u} 0 0).inv
    (joinStdSimplexIso.{u} 0 0).hom, Iso.inv_hom_id]
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma dgBarJoinCoconeLeg_yoneda {K : SSet.{u}} (x : K _⦋0⦌) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm x) (𝟙 (Δ[0] : SSet.{u}))) =
        F1B.joinCoconeLegSimplex x := by
  rw [SSet.yonedaEquiv_comp, dgBarJoinIntervalIdentity,
    F1B.joinCoconeLegSimplex_natural, SSet.yonedaEquiv_symm_app_id]

lemma dgBarUliftCoconeLegShape (K : SSet.{u}) (x : K _⦋0⦌) :
    (uliftCoconeShapeIso.{u, v} K 0).inv.app (Opposite.op ⦋1⦌)
      (F1B.joinCoconeLegSimplex (ULift.up x)) =
        ULift.up (F1B.joinCoconeLegSimplex x) := by
  rfl

lemma dgBarCoconeUlift_leg {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (x : K _⦋0⦌) :
    (c.ulift.{u, v}).val.app (Opposite.op ⦋1⦌)
      (F1B.joinCoconeLegSimplex (ULift.up x)) =
        ULift.up (c.val.app (Opposite.op ⦋1⦌) (F1B.joinCoconeLegSimplex x)) := by
  change ((SSet.uliftFunctor.{v, u}).map c.val).app (Opposite.op ⦋1⦌)
    ((uliftCoconeShapeIso K 0).inv.app _ (F1B.joinCoconeLegSimplex (ULift.up x))) = _
  rw [dgBarUliftCoconeLegShape]
  rfl

lemma dgBarTerminalNativeCocone_leg (R : Type u) (D : Type v)
    {J : Type u} [Category.{u} J] (j : J) :
    (dgBarTerminalNativeCocone R D (J := J)).val.app (Opposite.op ⦋1⦌)
      (F1B.joinCoconeLegSimplex (ULift.up (nerveEquiv.symm j))) =
        ULift.up (ComposableArrows.mk₁ (WithTerminal.homFrom j)) := by
  rw [dgBarTerminalNativeCocone, dgBarCoconeUlift_leg]
  exact congrArg ULift.up (F1B.nerveCocone_leg (F1B.withTerminalCocone J) j)

end SerrePositivity.InfinityCategories
