module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityKFlat
public import SerrePositivity.EInfinity.BarrattEccles.ModelCategory
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# セル代数の台の K 平坦性の還元

## 概要
Berger–Moerdijk 命題 4.1 の実際の転送モデルで、始対象からのセル付加を使う。

## 方針
重みに沿う分裂列の各商から K 平坦性を得る。小対象論法のセル代数から retract に戻す。

## 規約
重みの商の構成は別の入力。複体の上有界性は各商で使い、全体には要求しない。

## 使われ方
HA §3.2.2 の `baseChange_forget` と §3.2.4.7 のテンソル比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 次数ごとに分裂する重みのフィルトレーションでは、始段と各商の K 平坦性から
余極限の K 平坦性が従う。 -/
lemma carrierKFlat_of_splitFiltration {K : Complex A} (F : ℕ ⥤ Complex A)
    (e : K ≅ colimit F) (Q : ℕ → Complex A)
    (p : ∀ n, F.obj (n + 1) ⟶ Q n)
    (w : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ p n = 0)
    (split : ∀ n i, ((ShortComplex.mk _ _ (w n)).map
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i)).Splitting)
    (h0 : complexKFlat A (F.obj 0)) (hQ : ∀ n, complexKFlat A (Q n)) :
    complexKFlat A K := by
  have hF (n : ℕ) : complexKFlat A (F.obj n) := by
    induction n with
    | zero => exact h0
    | succ n ih =>
      exact complexKFlat_of_degreewiseSplit A (ShortComplex.mk _ _ (w n))
        (split n) ih (hQ n)
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact complexKFlat_of_iso A e (complexKFlat_colimit A F hF)

/-- セルのラベルを保持した小対象分解を使い、cofibrant 代数の台の K 平坦性を
始対象から付加したセル代数の各段に還元する。 -/
lemma cofibrantCarrierKFlat_of_cellStages
    (hstage :
      let P := operad A
      ∀ {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
        {Z W : P.Algebra} {g : Z ⟶ W}
        (t : RelativeCellComplex.{u}
          (fun (_ : J) (n : ℤ) => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) g),
        IsInitial Z → ∀ j, complexKFlat A (t.F.obj j).carrier)
    (X : (operad A).Algebra) :
    let := modelCategory A
    IsCofibrant X → complexKFlat A X.carrier := by
  dsimp only
  let := modelCategory A
  let P := operad A
  let I := (projectiveGeneratingCofibrations A).strictMap P.freeAlgebraFunctor
  let J := (projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor
  let U := Operad.Algebra.forget P
  let : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J := modelCategory_cofibrantlyGenerated A
  let : HasCoproducts.{u} P.Algebra := fun α =>
    (inferInstance : HasColimitsOfSize.{u, u} P.Algebra).has_colimits_of_shape (Discrete α)
  intro hX
  let f := initial.to X
  have hf : I.rlp.llp f := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J]
    let : IsCofibrant X := hX
    exact mem_cofibrations f
  obtain ⟨κ, hκ, hbot, hsmall⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal
    (I := I)
  let := hκ
  let := hbot
  let := hsmall
  let i := SmallObject.ιObj I κ f
  let p := SmallObject.πObj I κ f
  let t := SmallObject.relativeCellComplexιObj I κ f
  let generator (n : ℤ) := P.freeAlgebraFunctor.map (complexSphereToDisk A n)
  have hgen {Y Z : P.Algebra} (g : Y ⟶ Z) (hg : I g) :
      ∃ n, Arrow.mk g = Arrow.mk (generator n) := by
    cases hg with
    | map h =>
      cases h with
      | mk n => exact ⟨n, rfl⟩
  have hlabel (a : I.toSet) : ∃ n, Arrow.mk (I.homFamily a) = Arrow.mk (generator n) :=
    hgen (I.homFamily a) a.property
  let t' : RelativeCellComplex.{u} (fun (_ : κ.ord.ToType) => generator) i :=
    { toTransfiniteCompositionOfShape := t.toTransfiniteCompositionOfShape
      attachCells j hj := (t.attachCells j hj).reindexCellTypes generator
        (fun a => (hlabel a).choose) (fun a => eqToIso (hlabel a).choose_spec) }
  let sq : CommSq i f p (𝟙 X) := ⟨by simp [i, p]⟩
  have : HasLiftingProperty f p := hf p (SmallObject.rlp_πObj I κ f)
  let r : Retract X (SmallObject.obj I κ f) :=
    { i := sq.lift
      r := p
      retract := sq.fac_right }
  let hcol := isColimitOfPreserves U t'.isColimit
  let e := hcol.coconePointUniqueUpToIso (colimit.isColimit (t'.F ⋙ U))
  apply complexKFlat_of_retract A (r.map U)
  apply complexKFlat_of_iso A e
  exact complexKFlat_colimit A (t'.F ⋙ U) (hstage t' initialIsInitial)

end SerrePositivity.EInfinity.BarrattEccles
