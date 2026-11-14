module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# δ 環の通常のテンソル積

## 概要
通常の可換環の押し出しは δ 環の押し出しも与える。

## 方針
両因子からの Witt 長さ二の切断を、通常のテンソル積の普遍性で貼り合わせる。

## 規約
係数と両因子に p 正則性を仮定しない。

## 使われ方
BS 著者版 Corollary 3.12 と Proposition 3.13 (2) の完備押し出しの未完備部分。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w t

namespace SerrePositivity.BhattScholze

open scoped TensorProduct
open Algebra.TensorProduct

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

local notation "L" => (includeLeftRingHom : B →+* B ⊗[A] C)
local notation "R" => (includeRight.toRingHom : C →+* B ⊗[A] C)

private def tensorLift {T : Type t} [CommRing T] (f : B →+* T) (g : C →+* T)
    (h : f.comp (algebraMap A B) = g.comp (algebraMap A C)) : (B ⊗[A] C) →+* T :=
  let : Algebra A T := (f.comp (algebraMap A B)).toAlgebra
  let l : B →ₐ[A] T := { f with commutes' := fun _ ↦ rfl }
  let r : C →ₐ[A] T := { g with commutes' := fun a ↦ (DFunLike.congr_fun h a).symm }
  (productMap l r).toRingHom

private theorem tensorLift_left {T : Type t} [CommRing T] (f : B →+* T) (g : C →+* T)
    (h : f.comp (algebraMap A B) = g.comp (algebraMap A C)) :
    (tensorLift f g h).comp L = f := by
  let : Algebra A T := (f.comp (algebraMap A B)).toAlgebra
  let l : B →ₐ[A] T := { f with commutes' := fun _ ↦ rfl }
  let r : C →ₐ[A] T := { g with commutes' := fun a ↦ (DFunLike.congr_fun h a).symm }
  apply RingHom.ext
  intro b
  exact productMap_left_apply l r b

private theorem tensorLift_right {T : Type t} [CommRing T] (f : B →+* T) (g : C →+* T)
    (h : f.comp (algebraMap A B) = g.comp (algebraMap A C)) :
    (tensorLift f g h).comp R = g := by
  let : Algebra A T := (f.comp (algebraMap A B)).toAlgebra
  let l : B →ₐ[A] T := { f with commutes' := fun _ ↦ rfl }
  let r : C →ₐ[A] T := { g with commutes' := fun a ↦ (DFunLike.congr_fun h a).symm }
  apply RingHom.ext
  intro c
  exact productMap_right_apply l r c

private theorem wittTwoMap_comp_tensor {p : ℕ} [Fact p.Prime]
    {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z]
    (g : Y →+* Z) (f : X →+* Y) :
    (wittTwoMap (p := p) g).comp (wittTwoMap f) = wittTwoMap (g.comp f) := by
  apply RingHom.ext
  intro x
  apply TruncatedWittVector.ext
  intro i
  simp only [RingHom.comp_apply, wittTwoMap_coeff]

variable {p : ℕ} [Fact p.Prime]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (F : DeltaStructure p C)
variable (hE : D.IsDeltaHom E (algebraMap A B)) (hF : D.IsDeltaHom F (algebraMap A C))

include D hE hF

private theorem tensorSection_compatible :
    ((wittTwoMap L).comp E.sectionHom).comp (algebraMap A B) =
      ((wittTwoMap R).comp F.sectionHom).comp (algebraMap A C) := by
  have h₁ := (D.isDeltaHom_iff_sectionHom_comp E (algebraMap A B)).mp hE
  have h₂ := (D.isDeltaHom_iff_sectionHom_comp F (algebraMap A C)).mp hF
  have hb : (L).comp (algebraMap A B) = (R).comp (algebraMap A C) :=
    includeLeftRingHom_comp_algebraMap
  calc
    ((wittTwoMap L).comp E.sectionHom).comp (algebraMap A B) =
        (wittTwoMap ((L).comp (algebraMap A B))).comp D.sectionHom := by
      rw [RingHom.comp_assoc, ← h₁, ← RingHom.comp_assoc, wittTwoMap_comp_tensor]
    _ = (wittTwoMap ((R).comp (algebraMap A C))).comp D.sectionHom := by rw [hb]
    _ = ((wittTwoMap R).comp F.sectionHom).comp (algebraMap A C) := by
      rw [RingHom.comp_assoc, ← h₂, ← RingHom.comp_assoc, wittTwoMap_comp_tensor]

/-- 概要：δ 環の通常のテンソル積の δ 構造。
方針：Witt 長さ二の両切断は係数上で一致するので、環の押し出しで貼り合う。
規約：BS 著者版 Corollary 3.12 の通常の δ 環の押し出し。
使われ方：二元導来完備化へ移す前の環。 -/
def tensorDeltaStructure : DeltaStructure p (B ⊗[A] C) := by
  let f := (wittTwoMap L).comp E.sectionHom
  let g := (wittTwoMap R).comp F.sectionHom
  let h := tensorSection_compatible D E F hE hF
  let s := tensorLift f g h
  have hs : (wittTwoProjection p (B ⊗[A] C)).comp s = RingHom.id _ := by
    dsimp only [s]
    apply Algebra.TensorProduct.ringHom_ext
    · rw [RingHom.comp_assoc, tensorLift_left, RingHom.id_comp]
      apply RingHom.ext
      intro b
      simp [f, E.coeff_zero]
    · rw [RingHom.comp_assoc, tensorLift_right, RingHom.id_comp]
      apply RingHom.ext
      intro c
      simp [g, F.coeff_zero]
  exact ⟨s, fun x ↦ DFunLike.congr_fun hs x⟩

/-- 左因子の包含は δ 射。 -/
theorem tensorDeltaStructure_includeLeft :
    E.IsDeltaHom (tensorDeltaStructure D E F hE hF) L := by
  apply (E.isDeltaHom_iff_sectionHom_comp _ _).mpr
  exact (tensorLift_left _ _ (tensorSection_compatible D E F hE hF)).symm

/-- 右因子の包含は δ 射。 -/
theorem tensorDeltaStructure_includeRight :
    F.IsDeltaHom (tensorDeltaStructure D E F hE hF) R := by
  apply (F.isDeltaHom_iff_sectionHom_comp _ _).mpr
  exact (tensorLift_right _ _ (tensorSection_compatible D E F hE hF)).symm

/-- 概要：両因子で δ と可換な環射はテンソル積でも δ と可換。
方針：Witt 切断の二つの合成を両因子上で比較する。
規約：BS 著者版 Corollary 3.12 と Proposition 3.13 (2) の δ 押し出し。
使われ方：完備押し出しの試験射と一意性。 -/
theorem tensorDeltaStructure_isDeltaHom_iff {T : Type t} [CommRing T] (G : DeltaStructure p T)
    (k : (B ⊗[A] C) →+* T) :
    (tensorDeltaStructure D E F hE hF).IsDeltaHom G k ↔
      E.IsDeltaHom G (k.comp L) ∧ F.IsDeltaHom G (k.comp R) := by
  let H := tensorDeltaStructure D E F hE hF
  have hL := tensorDeltaStructure_includeLeft D E F hE hF
  have hR := tensorDeltaStructure_includeRight D E F hE hF
  refine ⟨fun h ↦ ⟨h.comp hL, h.comp hR⟩, ?_⟩
  rintro ⟨hl, hr⟩
  apply (H.isDeltaHom_iff_sectionHom_comp G k).mpr
  apply Algebra.TensorProduct.ringHom_ext
  · rw [RingHom.comp_assoc, RingHom.comp_assoc,
      ← (E.isDeltaHom_iff_sectionHom_comp H _).mp hL,
      ← RingHom.comp_assoc, wittTwoMap_comp_tensor,
      (E.isDeltaHom_iff_sectionHom_comp G _).mp hl]
  · rw [RingHom.comp_assoc, RingHom.comp_assoc,
      ← (F.isDeltaHom_iff_sectionHom_comp H _).mp hR,
      ← RingHom.comp_assoc, wittTwoMap_comp_tensor,
      (F.isDeltaHom_iff_sectionHom_comp G _).mp hr]

/-- 両脚に合う通常のテンソル積からの δ 射は一意に存在する。 -/
theorem existsUnique_tensorDeltaHom {T : Type t} [CommRing T] (G : DeltaStructure p T)
    (f : B →+* T) (g : C →+* T) (hf : E.IsDeltaHom G f) (hg : F.IsDeltaHom G g)
    (h : f.comp (algebraMap A B) = g.comp (algebraMap A C)) :
    ∃! k : (B ⊗[A] C) →+* T,
      (tensorDeltaStructure D E F hE hF).IsDeltaHom G k ∧ k.comp L = f ∧ k.comp R = g := by
  let k := tensorLift f g h
  have hl : k.comp L = f := tensorLift_left f g h
  have hr : k.comp R = g := tensorLift_right f g h
  refine ⟨k, ⟨(tensorDeltaStructure_isDeltaHom_iff D E F hE hF G k).mpr ?_, hl, hr⟩, ?_⟩
  · rw [hl, hr]
    exact ⟨hf, hg⟩
  · intro j hj
    exact Algebra.TensorProduct.ringHom_ext (hj.2.1.trans hl.symm) (hj.2.2.trans hr.symm)

end SerrePositivity.BhattScholze

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.7" (partial := special) "通常のテンソル積（p 正則性なし、BS-W15）、有向余極限、完全 δ 環のテンソル、w_R : R → W(R)（ghost 単射かつ p ねじれなしのとき）。一般の極限・余極限、W が右随伴であることは未 ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_tensorDeltaHom
attribute [cite BS19 "Rem 2.7" (partial := special) "通常のテンソル積（p 正則性なし、BS-W15）、有向余極限、完全 δ 環のテンソル、w_R : R → W(R)（ghost 単射かつ p ねじれなしのとき）。一般の極限・余極限、W が右随伴であることは未 ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.tensorDeltaStructure
