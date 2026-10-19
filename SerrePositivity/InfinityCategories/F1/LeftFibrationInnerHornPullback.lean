module

public import SerrePositivity.InfinityCategories.F1.ReplacementInnerHornPullback

/-!
概要：標準単体上の left fibration の内ホーンの逆像は前合成同値。
方針：底を有限鎖の nerve へ移し、逆像部分複体の等式で比較を戻す。
規約：モデル構造や平坦性を仮定しない。
使われ方：Kerodon Lemma 5.3.6.6、一般の inner anodyne 射の生成元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：部分複体による逆像と標準 pullback の包含は同じ前合成同値条件を持つ。
方針：標準 pullback 同型を合成または消去する。
規約：射 p の充填性は不要。
使われ方：標準単体と nerve の表示の変更に対応する。 -/
lemma isPrecompositionEquivalence_subcomplexInverseImage_iff
    {E B : SSet.{u}} (p : E ⟶ B) (A : B.Subcomplex) :
    IsPrecompositionEquivalence (A.preimage p).ι ↔
      IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  refine ⟨isPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage p A, ?_⟩
  intro h
  let hp := subcomplexInverseImage_isPullback p A
  have hh : hp.isoPullback.hom ≫ pullback.snd A.ι p = (A.preimage p).ι :=
    hp.isoPullback_hom_snd
  rw [← hh]
  exact (isPrecompositionEquivalence_of_iso hp.isoPullback).comp h

/-- 概要：標準単体上の left fibration の内ホーンの逆像部分複体の包含は前合成同値。
方針：有限鎖の nerve 上の結果を、二つの逆像部分複体の等式で移す。
規約：全空間 E は任意の universe u の単体集合。
使われ方：Kerodon Lemma 5.3.6.6 の生成ホーンの場合。 -/
lemma leftFibration_innerHorn_preimage_isPrecompositionEquivalence
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [LeftFibration p] :
    IsPrecompositionEquivalence ((horn n k).preimage p).ι := by
  let e := stdSimplex.isoNerve.{u} n
  let q := p ≫ e.hom
  have : LeftFibration q := ⟨leftFibrations.comp_mem _ _ (LeftFibration.mem (p := p))
    (MorphismProperty.of_isIso leftFibrations e.hom)⟩
  have h := (isPrecompositionEquivalence_subcomplexInverseImage_iff q
    (replacementNerveHorn n k)).2
      (leftFibration_nerveHorn_pullback_isPrecompositionEquivalence n k h0 hn q)
  have he : (replacementNerveHorn n k).preimage q = (horn n k).preimage p := by
    change ((horn n k).preimage e.inv).preimage (p ≫ e.hom) = _
    rw [← Subcomplex.preimage_comp, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  rw [he] at h
  exact h

/-- 概要：内ホーンの left fibration に沿う pullback の射影は前合成同値。
方針：逆像部分複体から標準 pullback に移し、射影の順序を交換する。
規約：射影は元の全空間 E へ向かう第一射影。
使われ方：Kerodon Lemma 5.3.6.6、inner anodyne の生成ホーンの逆像。 -/
lemma leftFibration_innerHorn_pullback_isPrecompositionEquivalence
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [LeftFibration p] :
    IsPrecompositionEquivalence (pullback.fst p (horn n k).ι) := by
  have h := (isPrecompositionEquivalence_subcomplexInverseImage_iff p (horn n k)).1
    (leftFibration_innerHorn_preimage_isPrecompositionEquivalence n k h0 hn p)
  have hc := (isPrecompositionEquivalence_of_iso (pullbackSymmetry p (horn n k).ι)).comp h
  rw [pullbackSymmetry_hom_comp_snd] at hc
  exact hc

end SerrePositivity.InfinityCategories
