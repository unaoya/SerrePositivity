module

public import SerrePositivity.KST.ProExcision.AdjacentCut

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 隣接する次数別商の間の境界

概要：隣接する項濾過の商の間の境界を、元の複体の微分と比較する。
方針：商の下端の標準同型で移し、包含で挟んだ分裂境界の計算を使う。
規約：シフトの成分同型を明示し、符号は Mathlib の分裂境界に従う。
使われ方：KST Lemma 4.10 の Koszul 係数微分の同定。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：隣接次数別商の間のシフトつき境界。
方針：右の短完全列の分裂境界に、左の商射のシフトを後合成する。
規約：a 次の商から a+1 次の商のシフトへ向かう。
使われ方：KST Lemma 4.10 の初頁微分のテンソル前の模型。 -/
def adjacentGradeBoundary (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentCutShortComplex P a).X₃ ⟶ (adjacentCutShortComplex P (a + 1)).X₃⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (adjacentCutShortComplex P a) (adjacentCutSplitting P a) ≫
    (adjacentCutShortComplex P (a + 1)).g⟦(1 : ℤ)⟧'

/-- 概要：隣接次数別商の下端の項を、元の複体の同じ項へ同定する。
方針：商射の下端での逆同型と、下端切り詰めの項同型を合成する。
規約：切り詰めの標準射に対応する同型。使われ方：KST Lemma 4.10 の係数の比較。 -/
def adjacentGradeTermIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentCutShortComplex P a).X₃.X a ≅ P.X a := by
  let : IsIso ((adjacentCutShortComplex P a).g.f a) :=
    projection_f_isIso (above P a) (a + 1 - 1) a (by omega)
  exact (asIso ((adjacentCutShortComplex P a).g.f a)).symm ≪≫
    aboveXIso P a a (le_refl _)

/-- 概要：隣接する次数別商の境界は、標準項同型で移すと元の複体の微分。
方針：下端の商射で前合成し、シフト比較・商射の逆・包含の自然性を簡約する。
規約：比較する成分は a から a+1。使われ方：KST Lemma 4.10 の係数微分の同定。 -/
theorem adjacentGradeBoundary_differential
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentGradeBoundary P a).f a ≫
      (CochainComplex.shiftFunctorObjXIso (adjacentCutShortComplex P (a + 1)).X₃
        1 a (a + 1) rfl).hom ≫
      (adjacentGradeTermIso P (a + 1)).hom =
        (adjacentGradeTermIso P a).hom ≫ P.d a (a + 1) := by
  let S := adjacentCutShortComplex P a
  let T := adjacentCutShortComplex P (a + 1)
  let : IsIso (S.g.f a) := projection_f_isIso (above P a) (a + 1 - 1) a (by omega)
  let : IsIso (T.g.f (a + 1)) :=
    projection_f_isIso (above P (a + 1)) (a + 1 + 1 - 1) (a + 1) (by omega)
  apply (cancel_epi (S.g.f a)).mp
  simp only [adjacentGradeBoundary, HomologicalComplex.comp_f, Category.assoc]
  rw [CochainComplex.shiftFunctor_map_f']
  rw [CochainComplex.homOfDegreewiseSplit_f]
  simp only [adjacentGradeTermIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom]
  erw [Category.id_comp]
  erw [IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
  erw [← inclusion_f P (a + 1) (a + 1) (le_refl _)]
  rw [← truncationInclusion_comp_inclusion P (a + 1) a (by omega)]
  simp only [HomologicalComplex.comp_f]
  erw [← inclusion_f P a a (le_refl _)]
  have hd := congrArg (fun f ↦ f ≫ (inclusion P a).f (a + 1))
    (adjacentCutBoundary_differential P a)
  simp only [Category.assoc] at hd
  exact hd.trans ((inclusion P a).comm a (a + 1)).symm

/-- 概要：隣接次数別商は下端以外の次数で零。
方針：下端より低い次数では元の下端切り詰め、高い次数では上端切り詰めの零性を使う。
規約：項ごとの零性。使われ方：KST Lemma 4.10 の一項複体模型。 -/
theorem adjacentGrade_isZero_X (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a q : ℤ) (hq : q ≠ a) : IsZero ((adjacentCutShortComplex P a).X₃.X q) := by
  by_cases hqa : q < a
  · exact (above_isZero_X P a q hqa).of_iso
      (belowXIso (above P a) (a + 1 - 1) q (by omega))
  · exact below_isZero_X (above P a) (a + 1 - 1) q (by omega)

/-- 概要：隣接次数別商を、標準項同型に対応する一項複体へ移す。
方針：唯一残る次数に項同型を使い、他の次数に零対象の同型を使う。
規約：下端の成分は adjacentGradeTermIso に一致する。
使われ方：KST Lemma 4.10 の微分を複体射として比較する。 -/
def adjacentGradeIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentCutShortComplex P a).X₃ ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj (P.X a) := by
  refine Hom.isoOfComponents (fun q ↦ if hq : q = a then ?_ else
    (adjacentGrade_isZero_X P a q hq).iso
      (isZero_single_obj_X (.up ℤ) a (P.X a) q hq)) ?_
  · subst q
    exact adjacentGradeTermIso P a ≪≫ (singleObjXSelf (.up ℤ) a (P.X a)).symm
  · intro i j hij
    by_cases hi : i = a
    · have hj : j ≠ a := by change i + 1 = j at hij; omega
      exact (isZero_single_obj_X (.up ℤ) a (P.X a) j hj).eq_of_tgt _ _
    · exact (adjacentGrade_isZero_X P a i hi).eq_of_src _ _

/-- 概要：次数別商から一項複体への同型の下端成分。
方針：同型を構成した成分を展開する。
規約：項同型の順序を固定する。使われ方：KST Lemma 4.10 の係数微分の比較。 -/
theorem adjacentGradeIso_hom_f (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentGradeIso P a).hom.f a = (adjacentGradeTermIso P a).hom ≫
      (singleObjXSelf (.up ℤ) a (P.X a)).inv := by
  simp [adjacentGradeIso]

/-- 概要：二つの隣接次数の一項複体の間の、指定された係数射を持つ境界。
方針：同じ次数の一項複体射に標準シフト同型の逆を合成する。
規約：シフトは 1。使われ方：KST Lemma 4.10 の元の微分から作る比較射。 -/
def singleDegreeBoundary {M N : ModuleCat.{u} R} (f : M ⟶ N) (a : ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M ⟶
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (a + 1)).obj N)⟦(1 : ℤ)⟧ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) a).map f ≫
    (((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso 1 a (a + 1) (by omega)).app N).inv

/-- 概要：一項複体境界の唯一残る成分は指定した係数射。
方針：一項複体と標準シフト同型の成分を展開する。
規約：両端の標準項同型を明示する。使われ方：KST Lemma 4.10 の微分の照合。 -/
theorem singleDegreeBoundary_f {M N : ModuleCat.{u} R} (f : M ⟶ N) (a : ℤ) :
    (singleDegreeBoundary f a).f a =
      (singleObjXSelf (.up ℤ) a M).hom ≫ f ≫ (singleObjXSelf (.up ℤ) (a + 1) N).inv := by
  unfold singleDegreeBoundary
  simp only [HomologicalComplex.comp_f]
  erw [single_map_f_self]
  simp [CochainComplex.singleFunctors, HomologicalComplex.single,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

/-- 概要：隣接次数別商の境界を一項複体へ移すと、元の微分から作った境界になる。
方針：下端成分で既証の微分公式を使い、他の次数は零性で比較する。
規約：標準シフト同型を含めて複体射として比較する。
使われ方：KST Lemma 4.10 の初頁の係数微分の複体レベルの同定。 -/
theorem adjacentGradeBoundary_single
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    adjacentGradeBoundary P a ≫ (adjacentGradeIso P (a + 1)).hom⟦(1 : ℤ)⟧' =
      (adjacentGradeIso P a).hom ≫ singleDegreeBoundary (P.d a (a + 1)) a := by
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q = a
  · subst q
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      adjacentGradeIso_hom_f, Category.assoc]
    rw [singleDegreeBoundary_f]
    have hd := adjacentGradeBoundary_differential P a
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hd
    erw [Category.id_comp] at hd
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hd, Category.assoc]
  · exact (adjacentGrade_isZero_X P a q hq).eq_of_src _ _

end SerrePositivity.KST.ProExcision
