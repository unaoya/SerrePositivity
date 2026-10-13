module

public import SerrePositivity.CLMST.Algebra
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 原典のテンソル積順序と同じ perfectoid 化

原典の D ⊗[A] A∞ から、既存の A∞ ⊗[A] D の perfectoid 化へ、
テンソル積の交換同型を通じた写像を構成する。選択した環を変更せず、
perfectoid 化の普遍性と D からの包含の一致を証明する。
存在引用に相対的な証明であり、新しい存在選択や引用は追加しない。
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- perfectoid 化の普遍性は、始域の環同型に沿う前合成で保たれる。 -/
theorem IsPerfectoidization.comp_ringEquiv {S S' C : Type u}
    [CommRing S] [CommRing S'] [CommRing C]
    {p : ℕ} [Fact p.Prime] {f : S →+* C}
    (hf : IsPerfectoidization p f) (e : S' ≃+* S) :
    IsPerfectoidization p (f.comp e.toRingHom) := by
  refine ⟨hf.1, ?_⟩
  intro T _ hT g
  obtain ⟨l, hl, hu⟩ := hf.2 T hT (g.comp e.symm.toRingHom)
  refine ⟨l, ?_, ?_⟩
  · ext x
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using
      DFunLike.congr_fun hl (e x)
  · intro l' hl'
    apply hu l'
    ext x
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using
      DFunLike.congr_fun hl' (e.symm x)

namespace CLMST
open Section2
open scoped TensorProduct

variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- 原典の D ⊗[A] A∞ から、既に選んだ RPerfd への写像。
交換同型の後に既存の普遍写像を適用し、新しい環を選択しない。 -/
noncomputable def toRPerfdOriginal :
    D ⊗[A] (CompletedTower A t p) →+* RPerfd A D t p hperf :=
  (toMixedPerfectoid A D t p hperf).comp
    (Algebra.TensorProduct.comm A D (CompletedTower A t p)).toRingHom

/-- 同じ RPerfd と原典のテンソル積順序からの写像は、perfectoid 化の普遍性を満たす。 -/
theorem isPerfectoidization_toRPerfdOriginal :
    IsPerfectoidization p (toRPerfdOriginal A D t p hperf) :=
  (isPerfectoidization_toMixedPerfectoid A D t p hperf).comp_ringEquiv
    (Algebra.TensorProduct.comm A D (CompletedTower A t p)).toRingEquiv

/-- 原典の左側 D の包含は、選んだ RPerfd 上の既存の D 作用と一致する。 -/
@[simp] theorem toRPerfdOriginal_comp_algebraMap :
    (toRPerfdOriginal A D t p hperf).comp
      (algebraMap D (D ⊗[A] (CompletedTower A t p))) =
        algebraMap D (RPerfd A D t p hperf) := rfl

/-- D の各元についても、原典の包含と既存の代数作用は同じ値を持つ。 -/
@[simp] theorem toRPerfdOriginal_algebraMap (d : D) :
    toRPerfdOriginal A D t p hperf
      (algebraMap D (D ⊗[A] (CompletedTower A t p)) d) =
        algebraMap D (RPerfd A D t p hperf) d := rfl

end CLMST
end SerrePositivity
