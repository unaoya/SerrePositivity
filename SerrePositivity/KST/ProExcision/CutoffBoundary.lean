module

public import SerrePositivity.KST.ProExcision.TensorBoundary

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 項切り詰めの境界は元の微分

概要：項ごと切り詰め短完全列の境界を、元の複体の微分へ同定する。
方針：境界の隣接する二項で包含と射影が同型であることを使う。
規約：分裂の符号と順序は Mathlib の cocycleOfDegreewiseSplit に従う。
使われ方：KST Lemma 4.10 の補助初頁微分の計算。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：項切り詰めの境界を元の複体の微分で計算する。
方針：下端の前後で射影と包含が同型となり、分裂の片側逆を両側逆へ移す。
規約：切り詰め位置は n+1、境界成分は n から n+1。
使われ方：KST Lemma 4.10 の初頁の Koszul 微分の同定。 -/
theorem cutoffBoundary_differential (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (StupidTruncation.shortComplex P (n + 1)).g.f n ≫
      (CochainComplex.cocycleOfDegreewiseSplit (StupidTruncation.shortComplex P (n + 1))
        (StupidTruncation.splitting P (n + 1))).1.v n (n + 1) rfl ≫
        (StupidTruncation.shortComplex P (n + 1)).f.f (n + 1) = P.d n (n + 1) := by
  let S := StupidTruncation.shortComplex P (n + 1)
  let σ := StupidTruncation.splitting P (n + 1)
  let : IsIso (S.f.f (n + 1)) := inclusion_f_isIso P (n + 1) (n + 1) (le_refl _)
  let : IsIso (S.g.f n) := projection_f_isIso P (n + 1 - 1) n (by omega)
  have hs : S.g.f n ≫ (σ n).s = 𝟙 (P.X n) := by
    apply (cancel_mono (S.g.f n)).mp
    erw [Category.assoc, (σ n).s_g, Category.comp_id]
  have hr : (σ (n + 1)).r ≫ S.f.f (n + 1) = 𝟙 (P.X (n + 1)) := by
    apply (cancel_epi (S.f.f (n + 1))).mp
    erw [← Category.assoc, (σ (n + 1)).f_r, Category.id_comp]
  change S.g.f n ≫ ((σ n).s ≫ P.d n (n + 1) ≫ (σ (n + 1)).r) ≫
    S.f.f (n + 1) = _
  erw [Category.assoc, Category.assoc, hr, Category.comp_id, ← Category.assoc, hs,
    Category.id_comp]

/-- 概要：項切り詰めのテンソル境界を包含・射影で比較すると元の微分のテンソルになる。
方針：一般のテンソル境界の同次公式と、切り詰め境界の微分計算を合成する。
規約：全次数 t=i+j と Koszul 方向の次数 i を区別する。
使われ方：KST Lemma 4.10 の初頁微分の具体的な計算。 -/
theorem cutoffTensorBoundary_differential
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j t : ℤ) (h : i + j = t) :
    ((StupidTruncation.shortComplex P (i + 1)).g.f i ▷ K.X j) ≫
      ιTensorObj (StupidTruncation.shortComplex P (i + 1)).X₃ K i j t h ≫
      (CochainComplex.cocycleOfDegreewiseSplit
        (cochainTensorShortComplexRight (StupidTruncation.shortComplex P (i + 1)) K)
        (cochainTensorShortComplexRightSplitting
          (StupidTruncation.shortComplex P (i + 1))
          (StupidTruncation.splitting P (i + 1)) K)).1.v t (t + 1) rfl ≫
      (cochainTensorMap (StupidTruncation.shortComplex P (i + 1)).f (𝟙 K)).f (t + 1) =
        (P.d i (i + 1) ▷ K.X j) ≫ ιTensorObj P K (i + 1) j (t + 1) (by omega) := by
  let S := StupidTruncation.shortComplex P (i + 1)
  let σ := StupidTruncation.splitting P (i + 1)
  have hd : S.g.f i ≫ ((σ i).s ≫ P.d i (i + 1) ≫ (σ (i + 1)).r) ≫
      S.f.f (i + 1) = P.d i (i + 1) := cutoffBoundary_differential P i
  rw [tensorSplitBoundary_homogeneous_assoc, ιTensorObj_cochainTensorMap]
  simp only [HomologicalComplex.id_f, tensorHom_id]
  erw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  erw [Category.assoc, hd]
  rfl

end SerrePositivity.KST.ProExcision
