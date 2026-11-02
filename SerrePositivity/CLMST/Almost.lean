module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.CommutativeAlgebra.Almost.Quotient

/-! # perfectoid ideal と mod p^N の almost 条件

perfectoid ideal を kernel の定義のまま p^N を法とした環へ写す。
その零化条件と元の環上の条件を、実際の商環作用によって比較する。
mod p^N の像イデアルの冪等性は独立した明示的な前提とし、
Bhatt--Scholze の basic setup の結果を証明済みとして組み込まない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- p^N を法とした環での perfectoid ideal の像。
元のイデアルは普遍 perfectoid 化への写像の核であり、根生成イデアルに置き換えない。 -/
abbrev perfectoidIdealMod (N : ℕ) : Ideal (R ⧸ Ideal.span {(p : R) ^ N}) :=
  (perfectoidIdeal R p hR g).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N}))

/-- p^N により零化される加群の商環作用で、perfectoid ideal の零化条件は変わらない。 -/
theorem perfectoidIdealMod_annihilates_iff (N : ℕ) (M : ModuleCat.{u} R)
    (hM : Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M) :
    let _ := Almost.quotientModule (Ideal.span {(p : R) ^ N}) M hM
    Almost.IsAlmostZero (perfectoidIdealMod R p hR g N) M ↔
      Almost.IsAlmostZero (perfectoidIdeal R p hR g) M :=
  Almost.isAlmostZero_quotient_iff (Ideal.span {(p : R) ^ N}) M
    (perfectoidIdeal R p hR g) hM

/-- mod p^N の像イデアルの冪等性が供給されれば、almost 圏の零性と元の kernel による零化が一致。
冪等性をこの接続の結論に隠さない。 -/
theorem isZero_perfectoidIdealMod_localization_iff (N : ℕ)
    [Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N)]
    (M : ModuleCat.{u} R) (hM : Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M) :
    let _ := Almost.quotientModule (Ideal.span {(p : R) ^ N}) M hM
    IsZero ((Almost.localization (perfectoidIdealMod R p hR g N)).obj
      (ModuleCat.of (R ⧸ Ideal.span {(p : R) ^ N}) M)) ↔
      Almost.IsAlmostZero (perfectoidIdeal R p hR g) M :=
  Almost.isZero_quotient_localization_obj_iff (Ideal.span {(p : R) ^ N})
    (perfectoidIdeal R p hR g) M hM

/-- mod p^N の almost 圏で線形写像が同型となる条件を、元の環の核・余核の零化条件へ移す。 -/
theorem isIso_perfectoidIdealMod_localization_iff (N : ℕ)
    [Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N)]
    {M M' : ModuleCat.{u} R}
    (hM : Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M)
    (hM' : Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M') (f : M ⟶ M') :
    let _ := Almost.quotientModule (Ideal.span {(p : R) ^ N}) M hM
    let _ := Almost.quotientModule (Ideal.span {(p : R) ^ N}) M' hM'
    IsIso ((Almost.localization (perfectoidIdealMod R p hR g N)).map
      (ModuleCat.ofHom (Almost.quotientLinearMap (Ideal.span {(p : R) ^ N}) hM hM' f.hom))) ↔
      Almost.IsAlmostIso (perfectoidIdeal R p hR g) f.hom :=
  Almost.isIso_quotient_localization_map_iff (Ideal.span {(p : R) ^ N})
    (perfectoidIdeal R p hR g) hM hM' f

omit [Fact p.Prime] in
/-- p が J に属すれば、一様な J 冪ねじれの二つの加群を同じ p の冪で零化できる。
mod p^N の almost 圏へ移す指数は仮定ではなく、各加群の冪ねじれから供給する。 -/
theorem exists_common_p_pow_annihilates (J : Ideal R) (hp : (p : R) ∈ J)
    (M M' : ModuleCat.{u} R) (hM : IsPowTorsion J M) (hM' : IsPowTorsion J M') :
    ∃ N : ℕ, Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M ∧
      Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M' := by
  obtain ⟨n, hn⟩ := hM
  obtain ⟨n', hn'⟩ := hM'
  refine ⟨n + n', ?_, ?_⟩
  · change Ideal.span {(p : R) ^ (n + n')} ≤ Module.annihilator R M
    rw [Ideal.span_singleton_le_iff_mem, Module.mem_annihilator]
    intro m
    rw [pow_add, mul_smul]
    exact hn (a := ⟨(p : R) ^ n, Ideal.pow_mem_pow hp n⟩)
  · change Ideal.span {(p : R) ^ (n + n')} ≤ Module.annihilator R M'
    rw [Ideal.span_singleton_le_iff_mem, Module.mem_annihilator]
    intro m
    rw [Nat.add_comm n n', pow_add, mul_smul]
    exact hn' (a := ⟨(p : R) ^ n', Ideal.pow_mem_pow hp n'⟩)

end SerrePositivity.CLMST
