module

public import SerrePositivity.KST.ProExcision.KoszulGraded
public import SerrePositivity.KST.ProExcision.CutoffBoundary

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 実際の隣接切り詰め射の短完全列

概要：二重切り詰めを除き、濾過で使った隣接射そのものを短完全列の第一射とする。
方針：標準の切り詰め短完全列との同型で分裂と完全性を移す。
規約：商複体と商射は標準模型から変えない。
使われ方：KST Lemma 4.10 の隣接三段への連結写像公式の適用。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：実際の隣接切り詰め射を第一射とする短複体。
方針：標準の二重切り詰めの包含を、二重切り詰めの逆同型で前合成する。
規約：商は標準の切り詰め商。使われ方：KST Lemma 4.10 の実際の濾過区間。 -/
def adjacentCutShortComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) := by
  let S := StupidTruncation.shortComplex (above P a) (a + 1)
  refine ShortComplex.mk (truncationInclusion P (a + 1) a (by omega)) S.g ?_
  rw [← aboveAboveIso_inv_comp_inclusion P (a + 1) a (by omega), Category.assoc]
  change (aboveAboveIso P (a + 1) a (by omega)).inv ≫ (S.f ≫ S.g) = 0
  rw [S.zero, comp_zero]

/-- 概要：実際の隣接短複体は標準の二重切り詰め短複体と同型。
方針：第一項に二重切り詰めの逆同型、他の二項に恒等同型を使う。
規約：商射の選択は変わらない。使われ方：KST Lemma 4.10 の分裂の移送。 -/
def adjacentCutIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    adjacentCutShortComplex P a ≅ StupidTruncation.shortComplex (above P a) (a + 1) := by
  refine ShortComplex.isoMk (aboveAboveIso P (a + 1) a (by omega)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · change (aboveAboveIso P (a + 1) a (by omega)).inv ≫ inclusion (above P a) (a + 1) =
      truncationInclusion P (a + 1) a (by omega) ≫ 𝟙 _
    rw [Category.comp_id]
    exact aboveAboveIso_inv_comp_inclusion P (a + 1) a (by omega)
  · change 𝟙 _ ≫ (StupidTruncation.shortComplex (above P a) (a + 1)).g =
      (StupidTruncation.shortComplex (above P a) (a + 1)).g ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- 概要：実際の隣接短複体の次数ごとの分裂。
方針：標準切り詰めの分裂を短複体の同型で移す。
規約：複体の分裂は主張しない。使われ方：KST Lemma 4.10 のテンソル境界。 -/
def adjacentCutSplitting (P : CochainComplex (ModuleCat.{u} R) ℤ) (a n : ℤ) :
    ((adjacentCutShortComplex P a).map (eval _ _ n)).Splitting :=
  (StupidTruncation.splitting (above P a) (a + 1) n).ofIso
    ((eval (ModuleCat.{u} R) (.up ℤ) n).mapShortComplex.mapIso (adjacentCutIso P a).symm)

/-- 概要：実際の隣接短複体は短完全。
方針：標準切り詰め短完全列の同型不変性を使う。
規約：元の複体に追加条件は不要。使われ方：KST Lemma 4.10 の cone–商比較。 -/
theorem adjacentCutShortComplex_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentCutShortComplex P a).ShortExact :=
  ShortComplex.shortExact_of_iso (adjacentCutIso P a).symm
    (stupidTruncation_module_shortExact (above P a) (a + 1))

/-- 概要：実際の隣接切り詰め短複体を係数複体とテンソルする。
方針：同じ全テンソル関手を三項と二射へ適用する。
規約：第一射は濾過で使う隣接射のテンソル。使われ方：KST Lemma 4.10 の隣接区間。 -/
def adjacentTensorCutShortComplex (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (adjacentCutShortComplex P a) K

/-- 概要：テンソル後の実際の隣接短複体の次数ごとの分裂。
方針：隣接短複体の次数ごとの分裂を全テンソルで移す。
規約：係数複体の平坦性は不要。使われ方：KST Lemma 4.10 の δ の明示的計算。 -/
def adjacentTensorCutSplitting (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a n : ℤ) :
    ((adjacentTensorCutShortComplex P K a).map (eval _ _ n)).Splitting :=
  cochainTensorShortComplexRightSplitting (adjacentCutShortComplex P a)
    (adjacentCutSplitting P a) K n

/-- 概要：テンソル後の実際の隣接短複体は短完全。
方針：次数ごとの分裂のテンソル保存を使う。
規約：一般のテンソル関手の完全性を仮定しない。使われ方：KST Lemma 4.10 の区間の商。 -/
theorem adjacentTensorCutShortComplex_shortExact
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentTensorCutShortComplex P K a).ShortExact :=
  cochainTensorShortComplexRight_shortExact (adjacentCutShortComplex P a)
    (adjacentCutSplitting P a) K

/-- 概要：隣接切り詰めの包含は残る次数で同型。
方針：元の複体への包含と合成し、二つの包含の同型性を使う。
規約：a 次以上でのみ主張する。使われ方：KST Lemma 4.10 の隣接境界計算。 -/
theorem truncationInclusion_f_isIso
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b q : ℤ)
    (hab : b ≤ a) (haq : a ≤ q) : IsIso ((truncationInclusion P a b hab).f q) := by
  let := inclusion_f_isIso P a q haq
  let := inclusion_f_isIso P b q (hab.trans haq)
  have he : (truncationInclusion P a b hab).f q ≫ (inclusion P b).f q =
      (inclusion P a).f q := congrArg (fun f ↦ f.f q)
        (truncationInclusion_comp_inclusion P a b hab)
  have : IsIso ((truncationInclusion P a b hab).f q ≫ (inclusion P b).f q) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((inclusion P b).f q)

/-- 概要：実際の隣接短完全列の境界を中央切り詰め複体の微分で表す。
方針：下端の商射と次の次数の包含が同型であることを一般境界公式へ渡す。
規約：標準短完全列から移した分裂を使用。
使われ方：KST Lemma 4.10 の実際の濾過の初頁微分。 -/
theorem adjacentCutBoundary_differential
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (adjacentCutShortComplex P a).g.f a ≫
      (CochainComplex.cocycleOfDegreewiseSplit (adjacentCutShortComplex P a)
        (adjacentCutSplitting P a)).1.v a (a + 1) rfl ≫
      (adjacentCutShortComplex P a).f.f (a + 1) = (above P a).d a (a + 1) := by
  let : IsIso ((adjacentCutShortComplex P a).g.f a) :=
    projection_f_isIso (above P a) (a + 1 - 1) a (by omega)
  let : IsIso ((adjacentCutShortComplex P a).f.f (a + 1)) :=
    truncationInclusion_f_isIso P (a + 1) a (a + 1) (by omega) (le_refl _)
  exact splitBoundary_differential (adjacentCutShortComplex P a) (adjacentCutSplitting P a) a

/-- 概要：実際の隣接濾過のテンソル境界を中央切り詰めの微分で計算する。
方針：隣接切り詰めの二次数での同型性を一般テンソル境界公式へ渡す。
規約：平坦性は不要。使われ方：KST Lemma 4.10 の初頁微分の同次成分。 -/
theorem adjacentTensorCutBoundary_differential
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a j t : ℤ) (h : a + j = t) :
    ((adjacentCutShortComplex P a).g.f a ▷ K.X j) ≫
      ιTensorObj (adjacentCutShortComplex P a).X₃ K a j t h ≫
      (CochainComplex.cocycleOfDegreewiseSplit (adjacentTensorCutShortComplex P K a)
        (adjacentTensorCutSplitting P K a)).1.v t (t + 1) rfl ≫
      (cochainTensorMap (adjacentCutShortComplex P a).f (𝟙 K)).f (t + 1) =
        ((above P a).d a (a + 1) ▷ K.X j) ≫
          ιTensorObj (above P a) K (a + 1) j (t + 1) (by omega) := by
  let : IsIso ((adjacentCutShortComplex P a).g.f a) :=
    projection_f_isIso (above P a) (a + 1 - 1) a (by omega)
  let : IsIso ((adjacentCutShortComplex P a).f.f (a + 1)) :=
    truncationInclusion_f_isIso P (a + 1) a (a + 1) (by omega) (le_refl _)
  exact splitTensorBoundary_differential (adjacentCutShortComplex P a)
    (adjacentCutSplitting P a) K a j t h

end SerrePositivity.KST.ProExcision
