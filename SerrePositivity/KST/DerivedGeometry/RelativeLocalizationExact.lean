module

public import SerrePositivity.KST.DerivedGeometry.BasicOpenLocalizationR

/-!
概要：基本開の被覆に沿う局所化による完全性の反映。
方針：局所的な像への帰属をイデアルの根基へ移し、基本開の定義元の可逆性で分母を払う。
規約：全空間の被覆・加群の有限性・係数の平坦性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の相対 Čech 完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [CommRing R]

/--
概要：基本開の被覆元がイデアルの根基に入れば、被覆先の定義元も根基に入る。
方針：イデアルの零点で被覆の等式を使い、素イデアルの根基性で矛盾を得る。
規約：被覆の有限性は不要。
使われ方：TT §3、Toën §3.2 の局所的な分母払い。
-/
lemma mem_radical_of_basicOpen_cover {ι : Type v} (a : R) (f : ι → R)
    (hcover : (⨆ i, basicOpen (f i)) = basicOpen a) (J : Ideal R)
    (hf : ∀ i, f i ∈ J.radical) : a ∈ J.radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical, mem_vanishingIdeal]
  intro p hp
  have hpJ : J ≤ p.asIdeal := (mem_zeroLocus _ _).mp hp
  by_contra ha
  have hx : p ∈ (⨆ i, basicOpen (f i)) := by
    rw [hcover]
    exact ha
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨n, hn⟩ := hf i
  exact hi (p.isPrime.mem_of_pow_mem n (hpJ hn))

/--
概要：局所化した短複体の核の元の像への帰属は定義元の冪を掛ければ大域化する。
方針：局所的な原像の分母と、局所化での等式の分母を順に払う。
規約：元の加群に有限性・平坦性を要求しない。
使われ方：TT §3、Toën §3.2 の相対完全性判定。
-/
lemma localizedExact_smul_pow_mem_range (T : ShortComplex (ModuleCat.{u} R)) (r : R)
    (he : (T.map (moduleLocalizationR (.powers r))).Exact) (y : T.X₂)
    (hy : T.g y = 0) : ∃ n : ℕ, r ^ n • y ∈ LinearMap.range T.f.hom := by
  let S := Submonoid.powers r
  let l₁ := LocalizedModule.mkLinearMap S T.X₁
  let l₂ := LocalizedModule.mkLinearMap S T.X₂
  let l₃ := LocalizedModule.mkLinearMap S T.X₃
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  have hly : IsLocalizedModule.map S l₂ l₃ T.g.hom (l₂ y) = 0 := by
    rw [IsLocalizedModule.map_apply, hy, map_zero]
  obtain ⟨z, hz⟩ := (hex (l₂ y)).mp hly
  change IsLocalizedModule.map S l₁ l₂ T.f.hom z = l₂ y at hz
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S l₁ z
  have hxy : l₂ (s • y) = l₂ (T.f x) := by
    rw [l₂.map_smul_of_tower, ← hz,
      ← (IsLocalizedModule.map S l₁ l₂ T.f.hom).map_smul_of_tower,
      hs, IsLocalizedModule.map_apply]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists S l₂).mp hxy
  obtain ⟨n, hn⟩ := (t * s).property
  change r ^ n = (t : R) * (s : R) at hn
  refine ⟨n, t • x, ?_⟩
  change T.f.hom (t • x) = r ^ n • y
  rw [T.f.hom.map_smul_of_tower, hn]
  simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using ht.symm

/--
概要：D(a) の被覆での局所化は a が可逆に作用する短複体の完全性を反映する。
方針：核の元の像への帰属イデアルの根基に a が入ることを使い、その冪を除く。
規約：最初の二項の可逆性だけを用い、全空間の被覆は仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の基本開の Čech 計算。
-/
lemma relativeBasicOpenLocalization_exact {ι : Type v} (a : R) (f : ι → R)
    (hcover : (⨆ i, basicOpen (f i)) = basicOpen a) (T : ShortComplex (ModuleCat.{u} R))
    (ha₁ : IsUnit (algebraMap R (Module.End R T.X₁) a))
    (ha₂ : IsUnit (algebraMap R (Module.End R T.X₂) a))
    (he : ∀ i, (T.map (moduleLocalizationR (.powers (f i)))).Exact) : T.Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  constructor
  · intro hy
    let J : Ideal R := (LinearMap.range T.f.hom).comap (LinearMap.toSpanSingleton R T.X₂ y)
    have hfi (i : ι) : f i ∈ J.radical := by
      obtain ⟨n, hn⟩ := localizedExact_smul_pow_mem_range T (f i) (he i) y hy
      exact ⟨n, hn⟩
    obtain ⟨n, hn⟩ := mem_radical_of_basicOpen_cover a f hcover J hfi
    obtain ⟨x, hx⟩ := hn
    have h₁ := (Module.End.isUnit_iff _).mp (show
      IsUnit (algebraMap R (Module.End R T.X₁) (a ^ n)) by simpa using ha₁.pow n)
    have h₂ := (Module.End.isUnit_iff _).mp (show
      IsUnit (algebraMap R (Module.End R T.X₂) (a ^ n)) by simpa using ha₂.pow n)
    obtain ⟨x', hx'⟩ := h₁.surjective x
    refine ⟨x', h₂.injective ?_⟩
    change a ^ n • T.f x' = a ^ n • y
    rw [← map_smul]
    exact (congrArg T.f hx').trans hx
  · rintro ⟨x, rfl⟩
    exact congrArg (fun k : T.X₁ ⟶ T.X₃ => k x) T.zero

end SerrePositivity.KST.DerivedGeometry
