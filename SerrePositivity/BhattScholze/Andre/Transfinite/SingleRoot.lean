module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicRootedExtension
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidTrialPrism
public import SerrePositivity.BhattScholze.Andre.Transfinite.Existence
open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre
open SerrePositivity.BhattScholze.Andre.Transfinite
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
環同型 R≃S による係数作用について、S は任意のイデアル I に関して R 上完全忠実平坦である。
BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）の一段拡大への適用。

## 方針
環同型を、元の R 作用と toAlgebra の作用の間の線形同型として扱い、R 自身の完全忠実平坦性を移す。

## 規約
環はすべて Type u。多項式は正次数モニックとし、p 正則性や追加の比較仮定は要求しない。
A1 の既証の有限 prism 商上の根付き拡大を使い、他レーンのファイルは変更しない。

## 使われ方
固定した多項式族を一元ずつ飽和させ、指定された任意族の step を構成する。
-/
theorem isCompletelyFaithfullyFlat_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    letI := e.toRingHom.toAlgebra; IsCompletelyFaithfullyFlat I S := by
  let := e.toRingHom.toAlgebra
  let E : R ≃ₗ[R] S :=
    { e.toAddEquiv with map_smul' := by intro r x; exact e.map_mul r x }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I E (isCompletelyFaithfullyFlat_self R I)
/-- ## 概要
任意の perfectoid 環 R 上の正次数モニック多項式は、p 完全忠実平坦な perfectoid 拡大で根を持つ。
BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）の一段拡大への適用。

## 方針
非零枝では既存の実 Fontaine・PD 構成による完全 prism 商表示に多項式を移し、
A1 の一元根付き拡大を適用する。元の基底との環同型が完全忠実平坦であることを示し、
標準射を合成する。零環枝では恒等射を使う。

## 規約
環はすべて Type u。多項式は正次数モニックとし、p 正則性や追加の比較仮定は要求しない。
A1 の既証の有限 prism 商上の根付き拡大を使い、他レーンのファイルは変更しない。

## 使われ方
固定した多項式族を一元ずつ飽和させ、指定された任意族の step を構成する。
-/
theorem exists_monicRootPerfectoidExtension (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (f : Polynomial R)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      f.eval₂ φ ρ = 0 := by
  classical
  rcases hR with hz | ⟨hp, hc, ⟨π, v, he⟩, hF, hk⟩
  · let := hz
    refine ⟨R, inferInstance, RingHom.id R, 0, Or.inl hz,
      isCompletelyFaithfullyFlat_self R _, Subsingleton.elim _ _⟩
  let := hc
  let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
  obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hk π v he
  let A := SerrePositivity.DerivedCompletion.PDCompletionH0 (WittVector p (PreTilt R p)) p d
  let := SerrePositivity.DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
  let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
    (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
  have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
    (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
  let Q := A ⧸ Ideal.span {P.generator}
  let F := f.map e.symm.toRingHom
  have hdegF : 0 < F.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
    exact hdeg
  obtain ⟨T, hTinst, φ, ρ, hT, hφ, hroot⟩ :=
    exists_monicRootPerfectoidExtension_of_perfectPrism P hP F (hf.map _) hdegF
  let := hTinst
  refine ⟨T, hTinst, φ.comp e.symm.toRingHom, ρ, hT,
    isCompletelyFaithfullyFlat_natCast_comp e.symm.toRingHom φ p
      (isCompletelyFaithfullyFlat_ringEquiv e.symm _) hφ, ?_⟩
  exact (Polynomial.eval₂_map _ _ _).symm.trans hroot
end SerrePositivity.BhattScholze.Andre.Transfinite
