module

public import SerrePositivity.BhattScholze.Delta.DeltaAdicEstimate
public import SerrePositivity.BhattScholze.Delta.DeltaResidueArithmetic
public import Mathlib.Algebra.MvPolynomial.Division

/-! # δ加法補正項の積可除性

整数係数の二変数で補正項を計算し、各変数での消滅から積可除性を得る。
第2有限δ関係式に必要な、通常射の下での補正項のδ像を制御する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- Witt第1加法補正項は二つの入力の積で割り切れる。 -/
theorem wittAdditionCarry_dvd_product (x y : A) :
    x * y ∣ (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
  let U := MvPolynomial Bool ℤ
  let X : U := MvPolynomial.X false
  let Y : U := MvPolynomial.X true
  let c : U := (WittVector.teichmuller p X + WittVector.teichmuller p Y).coeff 1
  have hx : X ∣ c := by
    apply Ideal.mem_span_singleton.mp
    have h := wittAdditionCarry_mem_of_right_mem (p := p) (Ideal.span {X}) Y X
      (Ideal.subset_span (by simp))
    simpa only [add_comm] using h
  have hy : Y ∣ c := by
    apply Ideal.mem_span_singleton.mp
    exact wittAdditionCarry_mem_of_right_mem (p := p) (Ideal.span {Y}) X Y
      (Ideal.subset_span (by simp))
  obtain ⟨z, hz⟩ := hx
  rw [hz] at hy
  have hyz : Y ∣ z := by
    rcases MvPolynomial.X_dvd_mul_iff.mp hy with hYX | hYz
    · have h := MvPolynomial.X_dvd_X.mp hYX
      exact Bool.noConfusion h
    · exact hYz
  obtain ⟨w, hw⟩ := hyz
  have hc : c = (X * Y) * w := by rw [hz, hw, mul_assoc]
  let f : U →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun b => if b then y else x)
  have hfX : f X = x := by
    exact MvPolynomial.eval₂Hom_X' (Int.castRingHom A) (fun b => if b then y else x) false
  have hfY : f Y = y := by
    exact MvPolynomial.eval₂Hom_X' (Int.castRingHom A) (fun b => if b then y else x) true
  have hfc : f c = (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
    change f ((WittVector.teichmuller p X + WittVector.teichmuller p Y).coeff 1) = _
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hfX, hfY]
  refine ⟨f w, ?_⟩
  have he := congrArg f hc
  simpa only [hfc, map_mul, hfX, hfY] using he

/-- 二つの入力がイデアルに属すれば、第1補正項はその平方に属する。 -/
theorem wittAdditionCarry_mem_square (I : Ideal A) (x y : A) (hx : x ∈ I) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I ^ 2 := by
  obtain ⟨z, hz⟩ := wittAdditionCarry_dvd_product (p := p) x y
  rw [hz]
  have hxy : x * y ∈ I ^ 2 := by simpa only [pow_two] using Ideal.mul_mem_mul hx hy
  exact (I ^ 2).mul_mem_right z hxy

/-- pと両入力を消す通常射の下では、第1補正項のδ像も消える。 -/
theorem DeltaStructure.map_delta_additionCarry_of_zero
    {B : Type v} [CommRing B] (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) (hx : q x = 0) (hy : q y = 0) :
    q (D.delta ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)) = 0 := by
  have hc := wittAdditionCarry_mem_square (p := p) (RingHom.ker q) x y hx hy
  have he := D.delta_mem_pow (RingHom.ker q) hp 1 _ hc
  simpa only [pow_one, RingHom.mem_ker] using he

/-- 第2δの加法公式：両入力と左のδ像が消える場合は補正項も消える。 -/
theorem DeltaStructure.map_delta_delta_add_of_zero
    {B : Type v} [CommRing B] (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) (hx : q x = 0) (hy : q y = 0)
    (hdx : q (D.delta x) = 0) :
    q (D.delta (D.delta (x + y))) = q (D.delta (D.delta x)) + q (D.delta (D.delta y)) := by
  let c := (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1
  have hc : q c = 0 := by
    change q ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) = 0
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hx, hy, WittVector.teichmuller_zero, add_zero,
      WittVector.zero_coeff]
  have hdc : q (D.delta c) = 0 := D.map_delta_additionCarry_of_zero q hp x y hx hy
  rw [D.delta_add]
  change q (D.delta (D.delta x + D.delta y + c)) = _
  rw [D.map_delta_add_of_right_zero q (D.delta x + D.delta y) c hc,
    D.map_delta_add_of_left_zero q (D.delta x) (D.delta y) hdx, hdc, add_zero]

/-- 通常射が差とその最初の二つのδ像を消せば、両元のδ²像は一致する。
右元の像が零であることを明示する。商のδ構造は仮定しない。 -/
theorem DeltaStructure.map_delta_delta_eq_of_difference_zero
    {B : Type v} [CommRing B] (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) (hy : q y = 0)
    (h0 : q (x - y) = 0) (h1 : q (D.delta (x - y)) = 0)
    (h2 : q (D.delta (D.delta (x - y))) = 0) :
    q (D.delta (D.delta x)) = q (D.delta (D.delta y)) := by
  have he := D.map_delta_delta_add_of_zero q hp (x - y) y h0 hy h1
  simpa only [sub_add_cancel, h2, zero_add] using he

end SerrePositivity.BhattScholze
