module

public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusKernel
public import SerrePositivity.CLMST.PerfectoidIdealRoots
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationUniqueness
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRepresentatives

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # perfectoid 商の Frobenius 比較への具体的な接続

mod p の Frobenius 全射性から根の代表元を取り、実際の商 Frobenius の単射性から
その代表元のイデアル所属を導く。反復Frobeniusの核はperfectoidの四条件から供給する。
選ばれたperfectoid化への全射性は別の条件として残し、普遍性と混同しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open Section2

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

/-- 実際の整perfectoid環と互換的なp冪根では、商の反復Frobeniusの単射性を四条件から供給できる。
零環は別に処理するため、pの非可逆性を明示する。 -/
theorem quotientRootFrobenius_injective_of_integralPerfectoid
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : S))]
    (hS : IsIntegralPerfectoid S p) (ρ : ℕ → S) (hρ₀ : ρ 0 = (p : S))
    (hρ : ∀ m, ρ (m + 1) ^ p = ρ m) (n : ℕ) :
    Function.Injective (quotientRootFrobenius S p n (ρ n)
      (by simpa only [zero_add, hρ₀] using compatibleRoots_pow p ρ hρ 0 n)) := by
  let hpRoot : ρ n ^ (p ^ n) = (p : S) := by
    simpa only [zero_add, hρ₀] using compatibleRoots_pow p ρ hρ 0 n
  let F := quotientRootFrobenius S p n (ρ n) hpRoot
  intro x y hxy
  have hz : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hrep⟩ := Ideal.Quotient.mk_surjective (x - y)
  rw [← hrep, quotientRootFrobenius_mk] at hz
  have hmem : z ^ (p ^ n) ∈ Ideal.span {(p : S)} := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hroot := (hS.pow_kernel_of_compatible_roots S p ρ hρ₀ hρ n z).mp hmem
  have hz0 : Ideal.Quotient.mk (Ideal.span {ρ n}) z = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hroot
  exact sub_eq_zero.mp (hrep.symm.trans hz0)

/-- 全射先がperfectoidなら、根の代表元はp冪根と写像の核が生成するイデアルに入る。
零環も含め、全射性によって根の係数を元環へ持ち上げる。 -/
theorem root_mem_sup_of_surjective_perfectoid
    {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (f : R →+* S) (hf : Function.Surjective f) (hS : IsIntegralPerfectoid S p)
    (ρ : ℕ → R) (hρ₀ : ρ 0 = (p : R)) (hρ : ∀ m, ρ (m + 1) ^ p = ρ m)
    (n : ℕ) (g x : R) (hg : f g = 0)
    (hx : x ^ (p ^ n) - g ∈ Ideal.span {(p : R)}) :
    x ∈ Ideal.span {ρ n} ⊔ RingHom.ker f := by
  rcases hS with hsub | hnonzero
  · let : Subsingleton S := hsub
    apply (show RingHom.ker f ≤ Ideal.span {ρ n} ⊔ RingHom.ker f from le_sup_right)
    exact Subsingleton.elim (f x) 0
  · let : Fact (¬ IsUnit (p : S)) := ⟨hnonzero.1⟩
    have hS : IsIntegralPerfectoid S p := Or.inr hnonzero
    have hxS : f x ^ (p ^ n) ∈ Ideal.span {(p : S)} := by
      have hmap := Ideal.mem_map_of_mem f hx
      rw [Ideal.map_span, Set.image_singleton, map_natCast] at hmap
      simpa only [map_sub, map_pow, hg, sub_zero] using hmap
    have hmem := (hS.pow_kernel_of_compatible_roots S p (fun m ↦ f (ρ m))
      (by rw [hρ₀, map_natCast]) (fun m ↦ by rw [← map_pow, hρ m]) n (f x)).mp hxS
    have hmem' : f x ∈ (Ideal.span {ρ n}).map f := by
      simpa only [Ideal.map_span, Set.image_singleton] using hmem
    change x ∈ Ideal.comap f ((Ideal.span {ρ n}).map f) at hmem'
    rwa [Ideal.comap_map_of_surjective f hf] at hmem'

/-- 選ばれたperfectoid化の標準写像が全射なら、式(4.0.10.1)が従う。
全射性は未供給の原典入力であり、ここでは明示的な仮定として扱う。 -/
theorem root_mem_sup_perfectoidIdeal_of_surjective
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hsurj : letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
      Function.Surjective
      (toPerfectoidization R (R ⧸ Ideal.span {g}) p hR))
    (ρ : ℕ → R) (hρ₀ : ρ 0 = (p : R)) (hρ : ∀ m, ρ (m + 1) ^ p = ρ m)
    (n : ℕ) (x : R) (hx : x ^ (p ^ n) - g ∈ Ideal.span {(p : R)}) :
    x ∈ Ideal.span {ρ n} ⊔ perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let f := (toPerfectoidization R (R ⧸ Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  exact root_mem_sup_of_surjective_perfectoid p f
    (hsurj.comp Ideal.Quotient.mk_surjective)
    (isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {g}) p hR).1
    ρ hρ₀ hρ n g x
    (by change toPerfectoidization R (R ⧸ Ideal.span {g}) p hR
          (Ideal.Quotient.mk (Ideal.span {g}) g) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero])
    hx

/-- pを座標に含む実際の完備塔では、全射性を供給すれば根の代表元と所属を同時に得る。
互換的な根の列は塔の構成から確認する。 -/
theorem exists_completed_root_mem_sup_perfectoidIdeal_of_surjective
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : CompletedTower A t p)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {g}) :=
        Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
      Function.Surjective (toPerfectoidization (CompletedTower A t p)
        (CompletedTower A t p ⧸ Ideal.span {g}) p hperf))
    (i : Fin h) (hti : t i = (p : A)) (n : ℕ) :
    ∃ x : CompletedTower A t p,
      x ^ (p ^ n) - g ∈ Ideal.span {(p : CompletedTower A t p)} ∧
      x ∈ Ideal.span {completedTowerRoot A t p n i} ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf g := by
  obtain ⟨x, hx⟩ := exists_root_mod_p_of_perfectoid _ p hperf n g
  refine ⟨x, hx, root_mem_sup_perfectoidIdeal_of_surjective _ p hperf g hsurj
    (fun m ↦ completedTowerRoot A t p m i) ?_
    (fun m ↦ completedTowerRoot_succ_pow A t p m i) n x hx⟩
  exact (CLMST.completedTowerRoot_zero A t p i).trans (by rw [hti, map_natCast])

/-- mod pで等しい代表元は、任意の冪を取ってもmod pで等しい。 -/
theorem pow_sub_mem_of_sub_mem {R : Type u} [CommRing R]
    (I : Ideal R) (x y : R) (k : ℕ) (hxy : x - y ∈ I) : x ^ k - y ^ k ∈ I := by
  have hq : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := Ideal.Quotient.eq.mpr hxy
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_pow, map_pow, hq, sub_self]

/-- 基底環の元のmod pのp冪根は、指定した段以降の有限段で合同式ごと代表できる。
この入口はperfectoid化への全射性を使わない。段の番号はFrobeniusの反復数と区別する。 -/
theorem exists_stage_root_mod_p_of_perfectoid
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A) (n m₀ : ℕ) :
    ∃ (m : ℕ) (_ : m₀ ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} := by
  obtain ⟨x, hx⟩ := exists_root_mod_p_of_perfectoid _ p hperf n
    (algebraMap A (CompletedTower A t p) g)
  obtain ⟨m, hm, z, hz⟩ := exists_completedTower_stage_representative A t p x 1 m₀
  rw [pow_one] at hz
  have hpow := pow_sub_mem_of_sub_mem _ _ _ (p ^ n) hz
  have heq : algebraMap (TowerStage A t p m) (CompletedTower A t p)
      (z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g) ∈
        Ideal.span {(p : CompletedTower A t p)} ^ 1 := by
    rw [pow_one, map_sub, map_pow,
      ← IsScalarTower.algebraMap_apply A (TowerStage A t p m) (CompletedTower A t p)]
    simpa only [sub_add_sub_cancel] using (Ideal.span {(p : CompletedTower A t p)}).add_mem hpow hx
  obtain ⟨l, hml, hl⟩ := exists_towerMap_mem_p_pow_of_completed A t p m 1 _ heq
  refine ⟨l, hm.trans hml, towerMap A t p m l hml z, ?_⟩
  simpa only [pow_one, map_sub, map_pow, AlgHom.commutes] using hl

/-- 有限段の根の合同式と、完備塔での式(4.0.10.1)の所属を同じ代表元で得る。
根の指数nと有限段mは区別し、mをnおよび指定した段以降に取る。 -/
theorem exists_stage_root_mem_sup_perfectoidIdeal_of_surjective
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (toPerfectoidization (CompletedTower A t p)
        (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))
    (i : Fin h) (hti : t i = (p : A)) (n m₀ : ℕ) :
    ∃ (m : ℕ) (_ : m₀ ≤ m) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} ∧
      algebraMap (TowerStage A t p m) (CompletedTower A t p) z ∈
        Ideal.span {completedTowerRoot A t p n i} ⊔
          perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) := by
  obtain ⟨m, hm, z, hz⟩ := exists_stage_root_mod_p_of_perfectoid A t p hperf g n (max m₀ n)
  refine ⟨m, (le_max_left _ _).trans hm, (le_max_right _ _).trans hm, z, hz, ?_⟩
  have hmap := Ideal.mem_map_of_mem
    (algebraMap (TowerStage A t p m) (CompletedTower A t p)) hz
  rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_pow,
    ← IsScalarTower.algebraMap_apply A (TowerStage A t p m) (CompletedTower A t p)] at hmap
  exact root_mem_sup_perfectoidIdeal_of_surjective _ p hperf _ hsurj
    (fun l ↦ completedTowerRoot A t p l i)
    ((CLMST.completedTowerRoot_zero A t p i).trans (by rw [hti, map_natCast]))
    (fun l ↦ completedTowerRoot_succ_pow A t p l i) n _ hmap

/-- perfectoid環で二つのp冪根がmod pで同じ値を持てば、その差は対応するp冪根に属する。
代表元を有限段で選び直す際の曖昧さを、同じ根イデアルの中で制御する。 -/
theorem sub_mem_root_span_of_pow_sub_mem_p
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R) (hρ₀ : ρ 0 = (p : R))
    (hρ : ∀ m, ρ (m + 1) ^ p = ρ m) (n : ℕ) (x y : R)
    (hxy : x ^ (p ^ n) - y ^ (p ^ n) ∈ Ideal.span {(p : R)}) :
    x - y ∈ Ideal.span {ρ n} := by
  rcases hR with hsub | hnonzero
  · let : Subsingleton R := hsub
    rw [Subsingleton.elim (x - y) 0]
    exact Ideal.zero_mem _
  · let : Fact (¬ IsUnit (p : R)) := ⟨hnonzero.1⟩
    have hR : IsIntegralPerfectoid R p := Or.inr hnonzero
    let q := Ideal.Quotient.mk (Ideal.span {(p : R)})
    let F := iterateFrobenius (R ⧸ Ideal.span {(p : R)}) p n
    have hpow : F (q x) = F (q y) := by
      apply sub_eq_zero.mp
      simpa only [q, F, iterateFrobenius_def, map_sub, map_pow] using
        Ideal.Quotient.eq_zero_iff_mem.mpr hxy
    apply (hR.pow_kernel_of_compatible_roots R p ρ hρ₀ hρ n (x - y)).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change F (q (x - y)) = 0
    rw [map_sub, map_sub, hpow, sub_self]

end SerrePositivity.CLMST
