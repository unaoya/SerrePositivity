module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.UnitValues
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
模型。文献の定義との比較は後で
# 区間余演算の複体射の単位則

概要：Berger–Fresse §2.2.6 の一文字単位の作用を全整数複体の射として証明する。
方針：左単位子の逆を前置し、二頂点・一辺の外延性で単位切断値へ帰着する。
規約：単位子と次数の零延長は既存のモノイダル複体のものを使う。
使われ方：区間の χ-coalgebra の unit_coaction。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：単位係数を前置した余演算の全次数評価（BF §2.2.6）。
方針：左単位子の逆、単位射の零成分、余演算の斉次成分を順に評価する。
規約：区間入力次数は任意の整数。
使われ方：単位則を頂点・辺生成元へ帰着する。 -/
lemma cochainAction_unit_input (r : ℤ) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A 1).f r
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).f r ((λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f r y)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A 1 0 r r (zero_add _)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 1 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A)) y := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.cochain_leftUnitor_inv_apply A,
    SerrePositivity.DifferentialGraded.whiskerRight_apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)
      0 r r (zero_add _) ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) y,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit_zero_apply, one_smul]
  exact congrArg (fun f => f
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 1 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A) ⊗ₜ[A] y))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ι_cochainAction A 1 0 r r (zero_add _))

/-- 概要：単位係数を前置した区間余演算は一次テンソル冪への標準同型（BF §2.2.6）。
方針：区間の非零二次数を生成元で比較し、残りは零対象で消す。
規約：全整数次数の複体射の等式。
使われ方：χ-coalgebra の単位則を標準単位子の文言へ直す。 -/
lemma cochainAction_unit_inv :
    (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A 1 =
      (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv := by
  apply HomologicalComplex.hom_ext
  intro r
  by_cases hr : r = 0
  · subst r
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInput_hom_ext A
    intro b
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A 1).f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).f 0
      ((λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b)))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_unit_input]
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_neg_vertex A 1 0
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 1 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b))
    simpa only [ModuleCat.hom_inv_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear_vertex,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_unitElement] using! h
  by_cases hr1 : r = -1
  · subst r
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInput_hom_ext A
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A 1).f (-1) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).f (-1)
      ((λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f (-1) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A)))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_unit_input]
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_neg_edge A 1 0
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 1 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.unitElement A)) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A))
    simpa only [ModuleCat.hom_inv_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputBilinear_edge,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_unitElement] using! h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have hy := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_eq_zero_of_other A r hr hr1 y
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A 1).f r ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).f r
      ((λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f r y)) = (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv.f r y
    simp only [hy, map_zero]

/-- 概要：区間余演算は χ の単位則を満たす（BF §2.2.6）。
方針：左単位子の逆で消去し、一次テンソル冪への標準同型を打ち消す。
規約：単位と右単位子は実際の複体射。
使われ方：Operad.Coalgebra の unit_coaction フィールド。 -/
lemma cochainAction_unit :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A 1 ≫ (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).hom =
      (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).hom := by
  apply (cancel_epi (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id] using
    congrArg (fun f => f ≫ (oneIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).hom) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_unit_inv A)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
