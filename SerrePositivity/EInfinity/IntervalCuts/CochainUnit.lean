module

public import SerrePositivity.EInfinity.IntervalCuts.UnitValues
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
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

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：単位係数を前置した余演算の全次数評価（BF §2.2.6）。
方針：左単位子の逆、単位射の零成分、余演算の斉次成分を順に評価する。
規約：区間入力次数は任意の整数。
使われ方：単位則を頂点・辺生成元へ帰着する。 -/
lemma cochainAction_unit_input (r : ℤ) (y : (interval A).X r) :
    (cochainAction A 1).f r
      ((complexUnit A ▷ interval A).f r ((λ_ (interval A)).inv.f r y)) =
      cochainActionBilinear A 1 0 r r (zero_add _)
        ((complexXIso A 1 0).inv (unitElement A)) y := by
  rw [BarrattEccles.cochain_leftUnitor_inv_apply A,
    SerrePositivity.DifferentialGraded.whiskerRight_apply (complexUnit A) (interval A)
      0 r r (zero_add _) ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) y,
    complexUnit_zero_apply, one_smul]
  exact congrArg (fun f => f
    ((complexXIso A 1 0).inv (unitElement A) ⊗ₜ[A] y))
      (ι_cochainAction A 1 0 r r (zero_add _))

/-- 概要：単位係数を前置した区間余演算は一次テンソル冪への標準同型（BF §2.2.6）。
方針：区間の非零二次数を生成元で比較し、残りは零対象で消す。
規約：全整数次数の複体射の等式。
使われ方：χ-coalgebra の単位則を標準単位子の文言へ直す。 -/
lemma cochainAction_unit_inv :
    (λ_ (interval A)).inv ≫ (complexUnit A ▷ interval A) ≫ cochainAction A 1 =
      (oneIso (interval A)).inv := by
  apply HomologicalComplex.hom_ext
  intro r
  by_cases hr : r = 0
  · subst r
    apply vertexInput_hom_ext A
    intro b
    change (cochainAction A 1).f 0 ((complexUnit A ▷ interval A).f 0
      ((λ_ (interval A)).inv.f 0 ((intervalXIso A 0).inv (vertexChain A b)))) = _
    rw [cochainAction_unit_input]
    have h := cochainActionBilinear_neg_vertex A 1 0
      ((complexXIso A 1 0).inv (unitElement A))
      ((intervalXIso A 0).inv (vertexChain A b))
    simpa only [ModuleCat.hom_inv_apply, vertexInputBilinear_vertex,
      vertexComponent_unitElement] using! h
  by_cases hr1 : r = -1
  · subst r
    apply edgeInput_hom_ext A
    change (cochainAction A 1).f (-1) ((complexUnit A ▷ interval A).f (-1)
      ((λ_ (interval A)).inv.f (-1) ((intervalXIso A 1).inv (edgeChain A)))) = _
    rw [cochainAction_unit_input]
    have h := cochainActionBilinear_neg_edge A 1 0
      ((complexXIso A 1 0).inv (unitElement A)) ((intervalXIso A 1).inv (edgeChain A))
    simpa only [ModuleCat.hom_inv_apply, edgeInputBilinear_edge,
      edgeComponent_unitElement] using! h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have hy := interval_eq_zero_of_other A r hr hr1 y
    change (cochainAction A 1).f r ((complexUnit A ▷ interval A).f r
      ((λ_ (interval A)).inv.f r y)) = (oneIso (interval A)).inv.f r y
    simp only [hy, map_zero]

/-- 概要：区間余演算は χ の単位則を満たす（BF §2.2.6）。
方針：左単位子の逆で消去し、一次テンソル冪への標準同型を打ち消す。
規約：単位と右単位子は実際の複体射。
使われ方：Operad.Coalgebra の unit_coaction フィールド。 -/
lemma cochainAction_unit :
    (complexUnit A ▷ interval A) ≫ cochainAction A 1 ≫ (oneIso (interval A)).hom =
      (λ_ (interval A)).hom := by
  apply (cancel_epi (λ_ (interval A)).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id] using
    congrArg (fun f => f ≫ (oneIso (interval A)).hom) (cochainAction_unit_inv A)

end SerrePositivity.EInfinity.IntervalCuts
