module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：整閉整域上の連結な étale 代数が整域となることを示す。
方針：一般ファイバーを有限個の体に分け、その冪等元を滑らかな整閉包の底変換で戻す。
規約：連結性は素スペクトルの連結性とする。
使われ方：体や離散付値環上の滑らかなチャートの連結成分を調べる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem idempotent_eq_zero_or_one_of_preconnected
    {B : Type*} [CommRing B] [PreconnectedSpace (PrimeSpectrum B)]
    {b : B} (hb : IsIdempotentElem b) : b = 0 ∨ b = 1 := by
  have ho : IsClopen (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨b, hb, rfl⟩
  rcases isClopen_iff.mp ho with h | h
  · left
    exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem hb (by simp [IsIdempotentElem])
      (SetLike.ext' (by simpa using h))
  · right
    exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem hb (by simp [IsIdempotentElem])
      (SetLike.ext' (by simpa using h))

private theorem isDomain_of_artinian_reduced_idempotents
    (D : Type*) [CommRing D] [Nontrivial D] [IsArtinianRing D] [IsReduced D]
    (h : ∀ d : D, IsIdempotentElem d → d = 0 ∨ d = 1) : IsDomain D := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := D)
  let i : MaximalSpectrum D := ⟨m, hm⟩
  let e := IsArtinianRing.equivPi D
  let s : ∀ j : MaximalSpectrum D, D ⧸ j.asIdeal := Pi.single i 1
  have hs : IsIdempotentElem s := by
    change s * s = s
    funext j
    by_cases hj : j = i
    · subst j
      simp [s]
    · simp [s, Pi.single_eq_of_ne hj]
  have hs' := h (e.symm s) (hs.map e.symm.toRingHom)
  have hsi : s i = 1 := by simp [s]
  have hall : ∀ j : MaximalSpectrum D, j = i := by
    have h1 : s = 1 := by
      rcases hs' with hz | hu
      · have he := congrArg e hz
        rw [e.apply_symm_apply, map_zero] at he
        exact (one_ne_zero (hsi.symm.trans (congrFun he i))).elim
      · simpa using congrArg e hu
    intro j
    by_contra hj
    have hzero : s j = 0 := Pi.single_eq_of_ne hj _
    exact zero_ne_one (hzero.symm.trans (congrFun h1 j))
  let : Field (D ⧸ i.asIdeal) := Ideal.Quotient.field _
  let π : D →+* (D ⧸ i.asIdeal) := (Pi.evalRingHom _ i).comp e.toRingHom
  apply Function.Injective.isDomain π
  intro x y hxy
  apply e.injective
  funext j
  rw [hall j]
  exact hxy

private theorem smooth_fractionTensor_injective
    (A B K : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K] [Algebra.Smooth A B] :
    Function.Injective (algebraMap B (B ⊗[A] K)) :=
  Algebra.TensorProduct.includeLeft_injective (R := A) (S := B) (A := B)
    (IsFractionRing.injective A K)

/--
概要：整閉整域上の滑らかな代数では、一般ファイバーの冪等元が一意に元の代数へ戻る。
方針：冪等元の整性と、滑らかな底変換による整閉包の比較を使う。
規約：一般ファイバーは基底の分数体へのテンソル積で表す。
使われ方：滑らかな族の一般ファイバーの開閉部分を、特殊化の議論に使う。
-/
theorem existsUnique_idempotent_of_smooth_fractionTensor
    {A B K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K] [Algebra.Smooth A B]
    (d : B ⊗[A] K) (hd : IsIdempotentElem d) :
    ∃! b : B, IsIdempotentElem b ∧ algebraMap B (B ⊗[A] K) b = d := by
  let D := B ⊗[A] K
  have hinj := smooth_fractionTensor_injective A B K
  have hi : IsIntegral B d := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · exact lt_of_le_of_lt Polynomial.degree_X_le (by decide)
    · simp [pow_two, hd.eq]
  have hsurj : Function.Surjective (algebraMap A (integralClosure A K)) := by
    intro z
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral z.2
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨z, hz⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := A) (S := B) (B := K)).2 ⟨d, hi⟩
  obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeLeft_surjective B B hsurj z
  have hbd : algebraMap B D b = d := by
    let h := (integralClosure B D).val.comp (TensorProduct.toIntegralClosure A B K)
    exact (h.commutes b).symm.trans (congrArg Subtype.val hz)
  have hb : IsIdempotentElem b := hinj (by rw [map_mul, hbd, hd.eq])
  exact ⟨b, ⟨hb, hbd⟩, fun c hc => hinj (hc.2.trans hbd.symm)⟩

/--
概要：整閉整域上の連結な滑らかなアフィン射は、一般ファイバーも連結。
方針：一般ファイバーの開閉部分を定める冪等元を持ち上げ、全空間の連結性を使う。
規約：連結性は素スペクトル上で表す。
使われ方：滑らかな射の切断を通る成分の特殊化を調べる。
-/
theorem connectedSpace_smooth_fractionTensor
    {A B K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K] [Algebra.Smooth A B]
    [ConnectedSpace (PrimeSpectrum B)] : ConnectedSpace (PrimeSpectrum (B ⊗[A] K)) := by
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial (B ⊗[A] K) := (smooth_fractionTensor_injective A B K).nontrivial
  refine connectedSpace_iff_clopen.mpr ⟨PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance, ?_⟩
  intro s hs
  obtain ⟨d, hd, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  obtain ⟨b, ⟨hb, rfl⟩, _⟩ := existsUnique_idempotent_of_smooth_fractionTensor d hd
  rcases idempotent_eq_zero_or_one_of_preconnected hb with rfl | rfl
  · left
    simp only [map_zero, PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot]
  · right
    simp only [map_one, PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]

/--
概要：整閉整域上の étale 代数のスペクトルが連結なら、その代数は整域。
方針：一般ファイバーは連結な有限 étale 代数なので体であり、元の代数はそこへ単射する。
規約：基底や代数の Noether 性を仮定しない。
使われ方：滑らかなファイバーの成分が整であることを étale チャートで示す。
-/
theorem isDomain_of_connected_etale_over_normal_domain
    {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [ConnectedSpace (PrimeSpectrum B)] : IsDomain B := by
  let K := FractionRing A
  let D := B ⊗[A] K
  let : Algebra.Etale K D := Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight A K B)
  let : Module.Finite K D := Algebra.FormallyUnramified.finite_of_free K D
  let : IsArtinianRing D := .of_finite K D
  let : IsReduced D := Algebra.FormallyUnramified.isReduced_of_field K D
  let : ConnectedSpace (PrimeSpectrum D) := connectedSpace_smooth_fractionTensor
  let : Nontrivial D := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : IsDomain D := isDomain_of_artinian_reduced_idempotents D
    (fun _ hd => idempotent_eq_zero_or_one_of_preconnected hd)
  exact Function.Injective.isDomain (algebraMap B D) (smooth_fractionTensor_injective A B K)

end SerrePositivity.AlgebraicGeometry
