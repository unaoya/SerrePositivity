module

public import SerrePositivity.KST.ProExcision.SpectralPro
public import SerrePositivity.HomologicalAlgebra.StupidTruncation
public import SerrePositivity.HomologicalAlgebra.CochainTensorCone
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

/-!
# Koszul 方向の項による濾過

概要：Koszul 複体の有限な方向を項ごとに切り詰めた濾過を構成する。
方針：元の Koszul 複体の切り詰めと既存の全テンソル複体を使う。
規約：通常の複体の濾過だけを構成する。
使われ方：KST Lemma 4.10 の 短完全列と長完全列への接続。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：項ごとの下端切り詰めの包含遷移。
方針：共通の項では恒等対応、消えた項では零射を使う。
規約：b ≤ a のとき a 次以上から b 次以上へ向かう。
使われ方：KST Lemma 4.10 の有限 Koszul 濾過。 -/
def truncationInclusion (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) : above K a ⟶ above K b := by
  let f (q : ℤ) : (above K a).X q ⟶ (above K b).X q :=
    if hq : a ≤ q then (aboveXIso K a q hq).hom ≫
      (aboveXIso K b q (hab.trans hq)).inv else 0
  have hf (q : ℤ) : f q ≫ (inclusion K b).f q = (inclusion K a).f q := by
    by_cases hq : a ≤ q
    · simp [f, hq, inclusion_f K a q hq, inclusion_f K b q (hab.trans hq)]
    · exact (above_isZero_X K a q (by omega)).eq_of_src _ _
  refine { f := f, comm' := ?_ }
  intro i j hij
  apply (cancel_mono ((inclusion K b).f j)).mp
  symm
  calc
    ((above K a).d i j ≫ f j) ≫ (inclusion K b).f j =
        (above K a).d i j ≫ (inclusion K a).f j := by rw [Category.assoc, hf]
    _ = (inclusion K a).f i ≫ K.d i j := ((inclusion K a).comm i j).symm
    _ = f i ≫ ((inclusion K b).f i ≫ K.d i j) := by rw [← hf i, Category.assoc]
    _ = (f i ≫ (above K b).d i j) ≫ (inclusion K b).f j := by
      rw [Category.assoc, ← (inclusion K b).comm]

/-- 概要：切り詰めの包含遷移は元の複体への包含と可換。
方針：共通の項と零項で比較する。規約：既存の切り詰め包含を使う。
使われ方：Koszul 濾過の関手律。 -/
theorem truncationInclusion_comp_inclusion (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hab : b ≤ a) :
    truncationInclusion K a b hab ≫ inclusion K b = inclusion K a := by
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : a ≤ q
  · simp [truncationInclusion, hq, inclusion_f K a q hq,
      inclusion_f K b q (hab.trans hq)]
  · exact (above_isZero_X K a q (by omega)).eq_of_src _ _

/-- 概要：下端を下げる項ごとの濾過を ℤ 上の関手にする。
方針：p 段を -p 次以上の切り詰めとする。
規約：p ≤ p' なら濾過は増大する。使われ方：KST Lemma 4.10 の Koszul 方向の濾過。 -/
def truncationFiltration (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj p := above K (-p)
  map {p q} h := truncationInclusion K (-p) (-q) (neg_le_neg h.le)
  map_id p := by
    have : Mono (inclusion K (-p)) := mono_of_mono_f _ (fun _ ↦ inferInstance)
    apply (cancel_mono (inclusion K (-p))).mp
    rw [truncationInclusion_comp_inclusion, Category.id_comp]
  map_comp {p q r} h k := by
    have : Mono (inclusion K (-r)) := mono_of_mono_f _ (fun _ ↦ inferInstance)
    apply (cancel_mono (inclusion K (-r))).mp
    rw [truncationInclusion_comp_inclusion, Category.assoc,
      truncationInclusion_comp_inclusion, truncationInclusion_comp_inclusion]

/-- 概要：Koszul 方向の項濾過を係数複体と全テンソルする。
方針：既存の複体のモノイダル構造の右テンソル関手を使う。
規約：Koszul の方向は列長により有限。使われ方：KST Lemma 4.10 の実際の濾過複体。 -/
def koszulTensorFiltration {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  truncationFiltration (koszulComplex z) ⋙ tensorRight K

/-- 概要：Koszul 方向の有限濾過の添字。
方針：Fin(e+2) の p を p-1 段へ送る。
規約：初段は一度以上で零、最終段は全 Koszul 複体。
使われ方：KST Lemma 4.10 の有限濾過の境界を含む索引。 -/
def koszulFiltrationIndex (e : ℕ) : Fin (e + 2) ⥤ ℤ :=
  (show Monotone (fun p : Fin (e + 2) ↦ (p.val : ℤ) - 1) from by
    intro p q hpq
    exact sub_le_sub_right (Int.ofNat_le.mpr hpq) 1).functor

/-- 概要：両端を含む有限な Koszul テンソル濾過。
方針：整数添字の濾過を Fin(e+2) に制限する。
規約：境界の零性・全体との同定は別の補題で確認する。
使われ方：KST Lemma 4.10 の収束を有限な問題へ帰着する。 -/
def finiteKoszulTensorFiltration {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Fin (e + 2) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  koszulFiltrationIndex e ⋙ koszulTensorFiltration z K

/-- 概要：Koszul 複体を一度以上で切り詰めると零複体になる。
方針：残る正次数は Koszul の上界で消え、他の次数は切り詰めで消える。
規約：係数環の Noether 性は不要。使われ方：KST Lemma 4.10 の濾過の初端。 -/
theorem koszulTruncation_initial_isZero {e : ℕ} (z : Fin e → R) :
    IsZero (above (koszulComplex z) 1) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext q
  have hz : IsZero ((above (koszulComplex z) 1).X q) := by
    by_cases hq : 1 ≤ q
    · exact IsZero.of_iso (koszulComplex_isZero_X_of_pos z q (by omega))
        (aboveXIso (koszulComplex z) 1 q hq)
    · exact above_isZero_X (koszulComplex z) 1 q (by omega)
  exact hz.eq_of_src _ _

/-- 概要：Koszul 列長の下界での切り詰めは全体と同型。
方針：下界以上では包含が同型、下界未満では両方の項が零。
規約：実際の包含を同型とする。使われ方：KST Lemma 4.10 の濾過の終端。 -/
theorem koszulTruncation_terminal_isIso {e : ℕ} (z : Fin e → R) :
    IsIso (inclusion (koszulComplex z) (-(e : ℤ))) := by
  have (q : ℤ) : IsIso ((inclusion (koszulComplex z) (-(e : ℤ))).f q) := by
    by_cases hq : -(e : ℤ) ≤ q
    · exact inclusion_f_isIso (koszulComplex z) (-(e : ℤ)) q hq
    · exact (above_isZero_X (koszulComplex z) (-(e : ℤ)) q (by omega)).isIso
        (koszulComplex_isZero_X_of_lt z q (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 概要：Koszul 方向の初端は任意の係数複体とのテンソル後も零。
方針：複体の右テンソル関手の零対象保存を使う。
規約：係数複体の平坦性・有界性は不要。使われ方：KST Lemma 4.10 の有限濾過。 -/
theorem koszulTensorFiltration_initial_isZero {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsZero ((tensorRight K).obj (above (koszulComplex z) 1)) :=
  (tensorRight K).map_isZero (koszulTruncation_initial_isZero z)

end SerrePositivity.KST.ProExcision
