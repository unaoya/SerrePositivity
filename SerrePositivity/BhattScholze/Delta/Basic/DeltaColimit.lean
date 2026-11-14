module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.Colimit.Ring

/-!
# δ 環の極限と余極限（BS 著者版 Remark 2.7）

## 概要
δ 両立な遷移を持つ有向系の環余極限の δ 構造と普遍性。BS 著者版 Remark 2.7 の有向余極限の場合。

## 方針
各段の W₂ 切断を Mathlib の Ring.DirectLimit.lift で貼り合わせる。

## 規約
一般のテンソル積・積・引き戻しは未形式化（A0 で同じ方法でここに足す）。

## 使われ方
δ 完全化（Perfect）、André の ω₁ 反復、d で割る包の有限部分族の余極限。
-/

@[expose] public noncomputable section
universe u v w

/-! ## 環余極限のδ構造

各段のW₂切断を、δと両立する遷移に沿ってMathlibの同じ環余極限へ移す。
遷移関数を別表現に置き換えず、標準段射と適合する普遍射のδ両立性を供給する。
-/

section DeltaDirectLimit

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i → A j) (D : ∀ i, DeltaStructure p (A i))
variable (hδ : ∀ i j hij x, f i j hij ((D i).delta x) = (D j).delta (f i j hij x))

/-- 各段の切断を標準段射で写し、環余極限上へ延長したW₂切断。 -/
def deltaDirectLimitSection : Ring.DirectLimit A f →+* WittTwo p (Ring.DirectLimit A f) :=
  Ring.DirectLimit.lift A f _
    (fun i ↦ (wittTwoMap (Ring.DirectLimit.of A f i)).comp (D i).sectionHom) (by
      intro i j hij x
      apply TruncatedWittVector.ext
      intro k
      fin_cases k
      · simp only [RingHom.comp_apply, wittTwoMap_coeff]
        change Ring.DirectLimit.of A f j (((D j).sectionHom (f i j hij x)).coeff 0) =
          Ring.DirectLimit.of A f i (((D i).sectionHom x).coeff 0)
        rw [(D j).coeff_zero, (D i).coeff_zero]
        exact Ring.DirectLimit.of_f hij x
      · simp only [RingHom.comp_apply, wittTwoMap_coeff]
        change Ring.DirectLimit.of A f j ((D j).delta (f i j hij x)) =
          Ring.DirectLimit.of A f i ((D i).delta x)
        rw [← hδ i j hij x]
        exact Ring.DirectLimit.of_f hij ((D i).delta x))

/-- 余極限の切断は標準段射上で元の切断をW₂へ写したものに一致する。 -/
@[simp] theorem deltaDirectLimitSection_of (i : ι) (x : A i) :
    deltaDirectLimitSection A f D hδ (Ring.DirectLimit.of A f i x) =
      wittTwoMap (Ring.DirectLimit.of A f i) ((D i).sectionHom x) :=
  Ring.DirectLimit.lift_of _ _ _ i x

/-- 余極限の切断の第0座標は恒等射。非空性や有向性を使わず段射上で比較する。 -/
theorem deltaDirectLimitSection_projection :
    (wittTwoProjection p (Ring.DirectLimit A f)).comp (deltaDirectLimitSection A f D hδ) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro i
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, deltaDirectLimitSection_of,
    wittTwoProjection_apply, wittTwoMap_coeff, (D i).coeff_zero, RingHom.id_apply]

/-- δと両立する遷移から得る、同じ環余極限上のδ構造（BS 著者版 Remark 2.7 の有向直系の余極限の δ 構造）。 -/
def deltaDirectLimitStructure : DeltaStructure p (Ring.DirectLimit A f) where
  sectionHom := deltaDirectLimitSection A f D hδ
  coeff_zero := by
    intro x
    exact RingHom.congr_fun (deltaDirectLimitSection_projection A f D hδ) x

/-- 余極限上のδは各段で元のδを計算する。 -/
@[simp] theorem deltaDirectLimitStructure_delta_of (i : ι) (x : A i) :
    (deltaDirectLimitStructure A f D hδ).delta (Ring.DirectLimit.of A f i x) =
      Ring.DirectLimit.of A f i ((D i).delta x) := by
  change (deltaDirectLimitSection A f D hδ (Ring.DirectLimit.of A f i x)).coeff 1 = _
  rw [deltaDirectLimitSection_of, wittTwoMap_coeff]
  rfl

/-- 各段から環余極限への標準環射はδ射。 -/
theorem deltaDirectLimitOf_isDeltaHom (i : ι) :
    (D i).IsDeltaHom (deltaDirectLimitStructure A f D hδ) (Ring.DirectLimit.of A f i) := by
  intro x
  exact (deltaDirectLimitStructure_delta_of A f D hδ i x).symm

/-- 適合するδ射族からの既存環余極限の普遍射もδ射（BS 著者版 Remark 2.7 の有向直系の余極限の余錐射）。
非空性・有向性や遷移の単射性を要求しない。 -/
theorem deltaDirectLimitLift_isDeltaHom {B : Type w} [CommRing B]
    (E : DeltaStructure p B) (g : ∀ i, A i →+* B)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hgδ : ∀ i, (D i).IsDeltaHom E (g i)) :
    (deltaDirectLimitStructure A f D hδ).IsDeltaHom E (Ring.DirectLimit.lift A f B g hg) := by
  apply (DeltaStructure.isDeltaHom_iff_sectionHom_comp _ _ _).mpr
  apply Ring.DirectLimit.hom_ext
  intro i
  apply RingHom.ext
  intro x
  change wittTwoMap (Ring.DirectLimit.lift A f B g hg)
      (deltaDirectLimitSection A f D hδ (Ring.DirectLimit.of A f i x)) =
    E.sectionHom (Ring.DirectLimit.lift A f B g hg (Ring.DirectLimit.of A f i x))
  rw [deltaDirectLimitSection_of, Ring.DirectLimit.lift_of]
  apply TruncatedWittVector.ext
  intro k
  simp only [wittTwoMap_coeff, Ring.DirectLimit.lift_of]
  fin_cases k
  · change g i (((D i).sectionHom x).coeff 0) = (E.sectionHom (g i x)).coeff 0
    rw [(D i).coeff_zero, E.coeff_zero]
  · exact hgδ i x

end SerrePositivity.BhattScholze

end DeltaDirectLimit

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.7" (partial := special) "通常のテンソル積（p 正則性なし、BS-W15）、有向余極限、完全 δ 環のテンソル、w_R : R → W(R)（ghost 単射かつ p ねじれなしのとき）。一般の極限・余極限、W が右随伴であることは未 ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.deltaDirectLimitLift_isDeltaHom
attribute [cite BS19 "Rem 2.7" (partial := special) "通常のテンソル積（p 正則性なし、BS-W15）、有向余極限、完全 δ 環のテンソル、w_R : R → W(R)（ghost 単射かつ p ねじれなしのとき）。一般の極限・余極限、W が右随伴であることは未 ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.deltaDirectLimitStructure
