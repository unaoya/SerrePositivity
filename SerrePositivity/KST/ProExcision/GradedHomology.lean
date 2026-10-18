module

public import SerrePositivity.KST.ProExcision.ShiftedComparison

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 隣接商のホモロジーと係数微分

概要：項濾過の隣接商の境界は、ホモロジー上で元の複体の微分と係数ホモロジーのテンソルを誘導する。
方針：商の一項模型の複体射比較を、シフトつきホモロジー写像へ移す。
規約：隣接する元の二項だけに平坦性を仮定する。
使われ方：KST Lemma 4.10 の有限 Koszul 濾過の初頁微分。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：隣接次数別商のテンソルホモロジーを、元の項と係数ホモロジーのテンソルへ移す。
方針：商の一項複体同型をテンソルし、指定係数次数の一項ホモロジー比較へ続ける。
規約：a 次の項の平坦性を仮定。使われ方：KST Lemma 4.10 の E₁ の係数模型。 -/
def adjacentTensorGradeHomologyIso
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a q s : ℤ)
    [Module.Flat R (P.X a)] (hs : q - a = s) :
    (adjacentTensorCutShortComplex P K a).X₃.homology q ≅
      (tensorLeft (P.X a)).obj (K.homology s) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
      ((cochainTensorFixedRight K).mapIso (adjacentGradeIso P a)) ≪≫
    singleTensorHomologyIsoAt (P.X a) K a q s hs

/-- 概要：隣接商のテンソル境界は、共通係数次数のホモロジーで元の微分のテンソルを誘導する。
方針：一項模型での複体射の等式をホモロジーへ移し、一項境界の係数比較を合成する。
規約：二つの元の項は平坦、係数複体は任意。
使われ方：KST Lemma 4.10 の初頁微分を Koszul 微分へ同定する。 -/
theorem adjacentTensorGradeHomology_differential
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a q q' s : ℤ)
    [Module.Flat R (P.X a)] [Module.Flat R (P.X (a + 1))]
    (hq : q + 1 = q') (hs : q - a = s) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (adjacentTensorGradeBoundary P K a) q q' (by omega) ≫
      (adjacentTensorGradeHomologyIso P K (a + 1) q' s (by omega)).hom =
      (adjacentTensorGradeHomologyIso P K a q s hs).hom ≫
        (P.d a (a + 1) ▷ K.homology s) := by
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let eM := (cochainTensorFixedRight K).map (adjacentGradeIso P a).hom
  let eN := (cochainTensorFixedRight K).map (adjacentGradeIso P (a + 1)).hom
  let tM := (singleTensorHomologyIsoAt (P.X a) K a q s hs).hom
  let tN := (singleTensorHomologyIsoAt (P.X (a + 1)) K (a + 1) q' s (by omega)).hom
  have h := congrArg (fun f ↦ H.shiftMap f q q' (by omega))
    (adjacentTensorGradeBoundary_single P K a)
  rw [H.shiftMap_comp, H.shiftMap_comp'] at h
  change H.shiftMap (adjacentTensorGradeBoundary P K a) q q' (by omega) ≫
      (homologyMap eN q' ≫ tN) =
    (homologyMap eM q ≫ tM) ≫ (P.d a (a + 1) ▷ K.homology s)
  calc
    _ = (H.shiftMap (adjacentTensorGradeBoundary P K a) q q' (by omega) ≫
        homologyMap eN q') ≫ tN := (Category.assoc _ _ _).symm
    _ = (homologyMap eM q ≫ H.shiftMap
        (tensorSingleDegreeBoundary (P.d a (a + 1)) K a) q q' (by omega)) ≫ tN :=
      congrArg (fun f ↦ f ≫ tN) h
    _ = homologyMap eM q ≫ (H.shiftMap
        (tensorSingleDegreeBoundary (P.d a (a + 1)) K a) q q' (by omega) ≫ tN) :=
      Category.assoc _ _ _
    _ = homologyMap eM q ≫ (tM ≫ (P.d a (a + 1) ▷ K.homology s)) :=
      congrArg (fun f ↦ homologyMap eM q ≫ f)
        (tensorSingleHomology_boundary_at (P.d a (a + 1)) K a q q' s hq hs)
    _ = _ := (Category.assoc _ _ _).symm

end SerrePositivity.KST.ProExcision
