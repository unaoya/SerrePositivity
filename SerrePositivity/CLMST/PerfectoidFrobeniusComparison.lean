module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # perfectoid 商の Frobenius 比較への具体的な接続

mod p の Frobenius 全射性から根の代表元を取り、実際の商 Frobenius の単射性から
その代表元のイデアル所属を導く。後者の単射性を perfectoid の四条件から導く
BMS Lemma 3.10 の部分は未実装であり、このファイルでは証明済みと扱わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST

/-- 冪写像の反復は、指数を反復した冪写像。 -/
theorem iterate_pow_apply {S : Type u} [Monoid S] (p m : ℕ) (x : S) :
    ((fun y : S ↦ y ^ p)^[m]) x = x ^ (p ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- mod p の Frobenius が全射なら、任意の元の p^m 乗根の代表元を mod p で取れる。 -/
theorem exists_root_mod_p_of_surjective (R : Type u) [CommRing R] (p m : ℕ)
    (hF : Function.Surjective (fun x : R ⧸ Ideal.span {(p : R)} ↦ x ^ p)) (g : R) :
    ∃ x : R, x ^ (p ^ m) - g ∈ Ideal.span {(p : R)} := by
  obtain ⟨x, hx⟩ := hF.iterate m (Ideal.Quotient.mk (Ideal.span {(p : R)}) g)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [iterate_pow_apply, ← map_pow] at hx
  refine ⟨x, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, hx, sub_self]

/-- integral perfectoid の定義に含まれる全射性から根の代表元を取る。
零環の場合も許すが、単射性はこの補題の結論には含めない。 -/
theorem exists_root_mod_p_of_perfectoid (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (m : ℕ) (g : R) :
    ∃ x : R, x ^ (p ^ m) - g ∈ Ideal.span {(p : R)} := by
  rcases hR with hR | ⟨_, _, _, hF, _⟩
  · let : Subsingleton R := hR
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim ((0 : R) ^ (p ^ m) - g) 0]
    exact Ideal.zero_mem _
  · exact exists_root_mod_p_of_surjective R p m hF g

/-- π^(p^m)=p による、実際の商環間の Frobenius 射。
対象の mod p 商が標数 p であることを明示する。 -/
def quotientRootFrobenius (S : Type u) [CommRing S] (p m : ℕ) [Fact p.Prime]
    [CharP (S ⧸ Ideal.span {(p : S)}) p] (π : S) (hπ : π ^ (p ^ m) = (p : S)) :
    S ⧸ Ideal.span {π} →+* S ⧸ Ideal.span {(p : S)} :=
  Ideal.Quotient.lift (Ideal.span {π})
    ((iterateFrobenius (S ⧸ Ideal.span {(p : S)}) p m).comp
      (Ideal.Quotient.mk (Ideal.span {(p : S)}))) (by
        change Ideal.span {π} ≤ RingHom.ker
          ((iterateFrobenius (S ⧸ Ideal.span {(p : S)}) p m).comp
            (Ideal.Quotient.mk (Ideal.span {(p : S)})))
        apply Ideal.span_le.mpr
        intro x hx
        have hxπ : x = π := Set.mem_singleton_iff.mp hx
        rw [hxπ]
        change (iterateFrobenius (S ⧸ Ideal.span {(p : S)}) p m)
          (Ideal.Quotient.mk (Ideal.span {(p : S)}) π) = 0
        rw [iterateFrobenius_def, ← map_pow, hπ]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

@[simp] theorem quotientRootFrobenius_mk (S : Type u) [CommRing S] (p m : ℕ) [Fact p.Prime]
    [CharP (S ⧸ Ideal.span {(p : S)}) p] (π : S) (hπ : π ^ (p ^ m) = (p : S)) (x : S) :
    quotientRootFrobenius S p m π hπ (Ideal.Quotient.mk (Ideal.span {π}) x) =
      Ideal.Quotient.mk (Ideal.span {(p : S)}) (x ^ (p ^ m)) := by
  simp [quotientRootFrobenius, iterateFrobenius_def]

/-- 原典式 (4.0.10.1) の図式追跡。
根の代表元と、R/I 上の実際の商 Frobenius 射の単射性から所属が従う。
R/I の perfectoid 性やその単射性を未知の一般構造に隠さない。 -/
theorem root_mem_sup_of_quotient_frobenius_injective
    (R : Type u) [CommRing R] (p m : ℕ) [Fact p.Prime] (I : Ideal R)
    [CharP ((R ⧸ I) ⧸ Ideal.span {(p : R ⧸ I)}) p]
    (π : R) (hπ : π ^ (p ^ m) = (p : R))
    (hF : Function.Injective (quotientRootFrobenius (R ⧸ I) p m
      (Ideal.Quotient.mk I π) (by rw [← map_pow, hπ]; exact map_natCast _ _)))
    (g x : R) (hg : g ∈ I) (hx : x ^ (p ^ m) - g ∈ Ideal.span {(p : R)}) :
    x ∈ Ideal.span {π} ⊔ I := by
  let f := Ideal.Quotient.mk I
  have hx' : f (x ^ (p ^ m)) ∈ Ideal.span {(p : R ⧸ I)} := by
    have hmap := Ideal.mem_map_of_mem f hx
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at hmap
    have hg0 : f g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
    simpa only [map_sub, hg0, sub_zero] using hmap
  have hzero : Ideal.Quotient.mk (Ideal.span {f π}) (f x) = 0 := by
    apply hF
    rw [quotientRootFrobenius_mk, map_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [map_pow] using hx'
  have hmem : f x ∈ (Ideal.span {π}).map f := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hpre := hmem
  change x ∈ Ideal.comap f ((Ideal.span {π}).map f) at hpre
  rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective] at hpre
  change x ∈ Ideal.span {π} ⊔ RingHom.ker f at hpre
  rw [Ideal.mk_ker] at hpre
  exact hpre

end SerrePositivity.CLMST
