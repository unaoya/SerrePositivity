module

public import SerrePositivity.KST.ProExcision.AdjacentGradeBoundary

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# テンソル後の次数別商の境界

概要：全テンソル後の隣接商境界を、元の複体の微分のテンソルへ比較する。
方針：分裂境界のテンソル公式と左シフト同型の自然性を合成する。
規約：係数複体の平坦性は不要。
使われ方：KST Lemma 4.10 の初頁微分を Koszul の係数微分へ移す。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：全テンソル後の隣接次数別商の間の境界。
方針：実際のテンソル短完全列の分裂境界に、次の商射のシフトを合成する。
規約：a 次の商から a+1 次の商のシフトへ向かう。
使われ方：KST Lemma 4.10 の実際の初頁微分の模型。 -/
def adjacentTensorGradeBoundary (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentTensorCutShortComplex P K a).X₃ ⟶
      (adjacentTensorCutShortComplex P K (a + 1)).X₃⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (adjacentTensorCutShortComplex P K a)
    (adjacentTensorCutSplitting P K a) ≫
      (cochainTensorMap (adjacentCutShortComplex P (a + 1)).g (𝟙 K))⟦(1 : ℤ)⟧'

/-- 概要：テンソル後の隣接商境界は、元の商境界のテンソルと標準シフト同型の合成。
方針：分裂境界のテンソル保存に、商射に関する左シフト比較の自然性を適用する。
規約：全複体射の等式。使われ方：KST Lemma 4.10 の微分のテンソル比較。 -/
theorem adjacentTensorGradeBoundary_eq
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    adjacentTensorGradeBoundary P K a =
      (cochainTensorFixedRight K).map (adjacentGradeBoundary P a) ≫
        (cochainTensorShiftLeft (adjacentCutShortComplex P (a + 1)).X₃ K 1).hom := by
  unfold adjacentTensorGradeBoundary
  erw [tensorSplitBoundary_eq]
  rw [Category.assoc, ← cochainTensorShiftLeft_naturality, ← Category.assoc]
  exact congrArg
    (fun f ↦ f ≫ (cochainTensorShiftLeft (adjacentCutShortComplex P (a + 1)).X₃ K 1).hom)
    ((cochainTensorFixedRight K).map_comp
      (CochainComplex.homOfDegreewiseSplit (adjacentCutShortComplex P a)
        (adjacentCutSplitting P a)) ((adjacentCutShortComplex P (a + 1)).g⟦(1 : ℤ)⟧')).symm

/-- 概要：指定された係数射を持つ一項境界を係数複体と全テンソルする。
方針：境界射をテンソルし、標準の左シフト同型を合成する。
規約：シフトは 1。使われ方：KST Lemma 4.10 の Koszul 微分の係数模型。 -/
def tensorSingleDegreeBoundary {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M) K ⟶
      (cochainTensor ((CochainComplex.singleFunctor (ModuleCat.{u} R) (a + 1)).obj N) K)⟦(1 : ℤ)⟧ :=
  (cochainTensorFixedRight K).map (singleDegreeBoundary f a) ≫
    (cochainTensorShiftLeft
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (a + 1)).obj N) K 1).hom

/-- 概要：全テンソル後の商境界を一項模型へ移すと、元の微分のテンソル境界になる。
方針：テンソル境界の比較とシフト同型の自然性に、テンソル前の複体射の等式を適用する。
規約：平坦性を仮定せず複体射として比較する。
使われ方：KST Lemma 4.10 の補助初頁微分と Koszul 微分の同定。 -/
theorem adjacentTensorGradeBoundary_single
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    adjacentTensorGradeBoundary P K a ≫
      ((cochainTensorFixedRight K).map (adjacentGradeIso P (a + 1)).hom)⟦(1 : ℤ)⟧' =
      (cochainTensorFixedRight K).map (adjacentGradeIso P a).hom ≫
        tensorSingleDegreeBoundary (P.d a (a + 1)) K a := by
  let F := cochainTensorFixedRight K
  let e := (adjacentGradeIso P a).hom
  let e' := (adjacentGradeIso P (a + 1)).hom
  let b := adjacentGradeBoundary P a
  let d := singleDegreeBoundary (P.d a (a + 1)) a
  let t := (cochainTensorShiftLeft
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) (a + 1)).obj (P.X (a + 1))) K 1).hom
  have hnat := cochainTensorShiftLeft_naturality (Q := K) e' 1
  have hmap : F.map b ≫ F.map (e'⟦(1 : ℤ)⟧') = F.map e ≫ F.map d := by
    calc
      F.map b ≫ F.map (e'⟦(1 : ℤ)⟧') = F.map (b ≫ e'⟦(1 : ℤ)⟧') :=
        (F.map_comp _ _).symm
      _ = F.map (e ≫ d) := congrArg F.map (adjacentGradeBoundary_single P a)
      _ = F.map e ≫ F.map d := F.map_comp _ _
  rw [adjacentTensorGradeBoundary_eq, Category.assoc]
  calc
    _ = F.map b ≫ (F.map (e'⟦(1 : ℤ)⟧') ≫ t) :=
      congrArg (fun f ↦ F.map b ≫ f) hnat.symm
    _ = (F.map b ≫ F.map (e'⟦(1 : ℤ)⟧')) ≫ t := (Category.assoc _ _ _).symm
    _ = (F.map e ≫ F.map d) ≫ t := congrArg (fun f ↦ f ≫ t) hmap
    _ = F.map e ≫ (F.map d ≫ t) := Category.assoc _ _ _

end SerrePositivity.KST.ProExcision
