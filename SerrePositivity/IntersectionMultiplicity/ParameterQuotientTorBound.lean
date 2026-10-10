module

public import SerrePositivity.IntersectionMultiplicity.ParameterQuotientTor
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.HomologicalAlgebra.NullHomotopy
public import SerrePositivity.LengthAlgebra.PerfectVanishing
public import SerrePositivity.PerfectComplex.BaseChange

/-!
# パラメータ商の `Tor` の消滅（論文 Lemma 5.3 の後半）

## 概要

`R` 代数 `C`（`φ`）、`L` の長さ `d` 以下の有限自由分解、`x_j L = 0`（`j = 1, …, h`）とする。
`C` 上の正規化長さ `λ` について Koszul ホモロジーの評価 `λ(H_q(x^v; C)) = 0`（`q > 0`、`v ≥ 1`）が
成り立てば

  `λ(Tor_i^R(C, L)) = 0`（`i > d − h`）。

論文 Lemma 5.3 の `τ_i(L) = 0`（`i > l = d − h`）。

## 方針

`P_C = C ⊗ P_L` に対して、`LengthAlgebra.lambdaHomology_projective_vanishing` を適用する。
`x_j L = 0` から共通の正の冪が `P_C` 上で零ホモトピックとなることを確認し、
環自身の Koszul 消滅と分解の長さを具体的入力として渡す。
長さの商におけるホモロジーの消滅は、共通の反復錐定理から従う。
零作用の錐では消去指数が増えないため、以前の `2^h` 倍の指数は不要。

下の `TorBound` 名前空間には既存の数値的評価も残す。上からの評価は
有限射影版の共通振幅補題の特殊例とし、主定理は数値的不等式を反復せずに証明する。

## 規約

複体は cochain（`ComplexShape.up ℤ`）。論文の homological 次数 `i` は cochain の `-i` 次。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ENNReal

namespace SerrePositivity

namespace TorBound

variable {C : Type u} [CommRing C]

/-- `a` がホモトピー圏で `X` 上の零写像として作用すること（`a • 𝟙 X` が零ホモトピック）。 -/
def Kills (a : C) (X : CochainComplex (ModuleCat.{u} C) ℤ) : Prop :=
  a • 𝟙 ((homotopyQuot C).obj X) = 0

/-- `X` 上で `a` が零なら、写像錐を `n` 回とった `K(z; X)` 上で `a^{2^n}` が零。 -/
lemma kills_koszulComplexOn {a : C} {X : CochainComplex (ModuleCat.{u} C) ℤ} (h : Kills a X) :
    ∀ {n : ℕ} (z : Fin n → C), Kills (a ^ 2 ^ n) (koszulComplexOn z X)
  | 0, z => by
    change Kills (a ^ 1) X
    rwa [pow_one]
  | n + 1, z => by
    have ih := kills_koszulComplexOn h (Fin.init z)
    have := mappingCone_smul_mul_self_eq_zero
      (smulId (z (Fin.last n)) (koszulComplexOn (Fin.init z) X)) (a ^ 2 ^ n) ih ih
    rw [← pow_add, ← two_mul, ← pow_succ'] at this
    exact this

/-- `K(z; X)` 上で `z_j^{2^n}` が零。 -/
lemma kills_koszulComplexOn_self (X : CochainComplex (ModuleCat.{u} C) ℤ) :
    ∀ {n : ℕ} (z : Fin n → C) (j : Fin n), Kills (z j ^ 2 ^ n) (koszulComplexOn z X)
  | 0, _, j => j.elim0
  | n + 1, z, j => by
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · have := mappingCone_smulId_mul_self_eq_zero
        (X := koszulComplexOn (Fin.init z) X) (z (Fin.last n))
      rw [← sq] at this
      exact pow_smul_id_eq_zero_of_le this
        (show 2 ≤ 2 ^ (n + 1) from
          (pow_one 2).symm.le.trans (Nat.pow_le_pow_right (by omega) (by omega)))
    · have ih := kills_koszulComplexOn_self X (Fin.init z) j
      have := mappingCone_smul_mul_self_eq_zero
        (smulId (z (Fin.last n)) (koszulComplexOn (Fin.init z) X)) _ ih ih
      rw [← pow_add, ← two_mul, ← pow_succ'] at this
      exact this

/-- `a` が `X` 上で零なら、`a` は `X` のホモロジーを消す。 -/
lemma Kills.smul_homology {a : C} {X : CochainComplex (ModuleCat.{u} C) ℤ} (h : Kills a X)
    (i : ℤ) (t : X.homology i) : a • t = 0 := by
  obtain ⟨H⟩ := (nonempty_homotopy_smul_id_zero_iff a X).mpr h
  have := H.homologyMap_eq i
  rw [HomologicalComplex.homologyMap_zero, homologyMap_smul, HomologicalComplex.homologyMap_id]
    at this
  exact congrArg (fun f ↦ f.hom t) this

variable {J : Ideal C} (lam : NormalizedLength C J)

/-- `y` の各元の冪が `X` 上で零で、`J ⊆ √(y)`（`J` は有限生成）なら、`X` のホモロジーは `J` 冪ねじれ。 -/
lemma isPowTorsion_homology {s : ℕ} {y : Fin s → C} (hfg : J.FG)
    (hJ : J ≤ (Ideal.span (Set.range y)).radical) {X : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : ∀ j, ∃ N, Kills (y j ^ N) X) (i : ℤ) : IsPowTorsion J (X.homology i) := by
  refine IsPowTorsion.of_le_radical_annihilator hfg (hJ.trans ?_)
  rw [← Ideal.radical_idem (Module.annihilator C (X.homology i))]
  refine Ideal.radical_mono ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨N, hN⟩ := h j
  exact ⟨N, Module.mem_annihilator.mpr (hN.smul_homology i)⟩

/-! ## 下からの評価 -/

variable {s : ℕ} {y : Fin s → C} (hfg : J.FG) (hJ : J ≤ (Ideal.span (Set.range y)).radical)

include hfg hJ in
/-- **下からの評価**：`y` の冪が `X` 上で零（ホモロジーのねじれのため）、各 `c_k` が `X` 上で零、
`e ≥ 2^n` なら `λ(H^{m+n}(X)) ≤ λ(H^m(K(c^e; X)))`。写像錐を一段とるごとに、`c_k^e` の作用は
ホモロジーで零なので連結射 `H^m(Cone) → H^{m+1}` が全射。 -/
theorem len_homology_le_koszulComplexOn (X : CochainComplex (ModuleCat.{u} C) ℤ)
    (hX : ∀ j, ∃ N, Kills (y j ^ N) X) :
    ∀ {n : ℕ} (c : Fin n → C) (_hc : ∀ k, Kills (c k) X) (e : ℕ) (_he : 2 ^ n ≤ e) (m : ℤ),
      lam.len (X.homology (m + n)) ≤
        lam.len ((koszulComplexOn (fun k ↦ c k ^ e) X).homology m)
  | 0, c, _, e, _, m => by
    change lam.len (X.homology (m + ((0 : ℕ) : ℤ))) ≤ lam.len (X.homology m)
    rw [Nat.cast_zero, add_zero]
  | n + 1, c, hc, e, he, m => by
    let K' := koszulComplexOn (fun k ↦ Fin.init c k ^ e) X
    let f := smulId (c (Fin.last n) ^ e) K'
    change lam.len (X.homology (m + ((n + 1 : ℕ) : ℤ))) ≤
      lam.len ((CochainComplex.mappingCone f).homology m)
    -- `f` はホモロジーで零
    have hkill : Kills (c (Fin.last n) ^ e) K' :=
      pow_smul_id_eq_zero_of_le (kills_koszulComplexOn (hc (Fin.last n)) _)
        ((Nat.pow_le_pow_right (by omega) (Nat.le_succ n)).trans he)
    have hf : HomologicalComplex.homologyMap f (m + 1) = 0 := by
      change HomologicalComplex.homologyMap (smulId (c (Fin.last n) ^ e) K') (m + 1) = 0
      ext t
      rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
      exact hkill.smul_homology (m + 1) t
    -- 連結射は全射
    have hex : Function.Exact (Cone.δ f m (m + 1) rfl).hom
        (HomologicalComplex.homologyMap f (m + 1)).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₁ f m (m + 1) rfl)
    have hδ : Function.Surjective (Cone.δ f m (m + 1) rfl).hom := by
      intro t
      exact (hex t).mp (by rw [hf]; rfl)
    -- ねじれ
    have ht : IsPowTorsion J ((CochainComplex.mappingCone f).homology m) :=
      isPowTorsion_homology hfg hJ (fun j ↦ by
        obtain ⟨N, hN⟩ := hX j
        exact ⟨N * 2 ^ (n + 1), by
          rw [pow_mul]; exact kills_koszulComplexOn hN (n := n + 1) (fun k ↦ c k ^ e)⟩) m
    have ih := len_homology_le_koszulComplexOn X hX (Fin.init c) (fun k ↦ hc _) e
      ((Nat.pow_le_pow_right (by omega) (Nat.le_succ n)).trans he) (m + 1)
    have hidx : m + ((n + 1 : ℕ) : ℤ) = m + 1 + (n : ℤ) := by push_cast; ring
    rw [hidx]
    exact ih.trans (lam.len_le_of_surjective _ hδ ht)

/-! ## 上からの評価 -/

section upper

variable {n : ℕ} (z : Fin n → C) (hJz : J ≤ (Ideal.span (Set.range z)).radical)
  (hz : ∀ q : ℕ, 0 < q → lam.len (koszulHomologySelf z q) = 0)

include hfg hJz in
/-- `K(z; Q)` のホモロジーは `J` 冪ねじれ（`z_j^{2^n}` が零）。 -/
lemma isPowTorsion_koszul (Q : CochainComplex (ModuleCat.{u} C) ℤ) (i : ℤ) :
    IsPowTorsion J ((koszulComplexOn z Q).homology i) :=
  isPowTorsion_homology hfg hJz (fun j ↦ ⟨2 ^ n, kills_koszulComplexOn_self Q z j⟩) i

/-- 零複体の `K(z; Q)` のホモロジーの長さは `0`。 -/
lemma len_koszul_isZero {Q : CochainComplex (ModuleCat.{u} C) ℤ} (hQ : IsZero Q) (i : ℤ) :
    lam.len ((koszulComplexOn z Q).homology i) = 0 := by
  have hz :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) i).map_isZero
      ((koszulFunctor z).map_isZero hQ)
  have : Subsingleton ((koszulComplexOn z Q).homology i) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact lam.len_eq_zero_of_subsingleton _

include hz in
/-- 環を `a` 次に置いた単一複体：`λ(H^m(K(z; C[−a]))) = 0`（`m < a`）。シフト同型で
`H_{a−m}(z; C)` に移す。 -/
lemma len_koszul_single_ring (a m : ℤ) (hm : m < a) :
    lam.len ((koszulComplexOn z
      ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C C))).homology m) = 0 := by
  let P := (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of C C)
  let e := ((CochainComplex.singleFunctors (ModuleCat.{u} C)).shiftIso (-a) a 0 (by omega)).app
    (ModuleCat.of C C)
  let eK : koszulComplexOn z ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C C)) ≅
      (koszulComplex z)⟦-a⟧ :=
    (koszulFunctor z).mapIso e.symm ≪≫ (koszulComplexOnShiftIso z P (-a)).symm ≪≫
      (shiftFunctor _ (-a)).mapIso (eqToIso (koszulComplexOn_single z))
  let eh :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) m).mapIso eK ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-a) m (m - a) (by omega)).app
      (koszulComplex z)
  refine (lam.len_congr _ _ eh.toLinearEquiv).trans ?_
  have hq : m - a = -(((a - m).toNat : ℕ) : ℤ) := by omega
  change lam.len ((koszulComplex z).homology (m - a)) = 0
  rw [hq]
  exact hz _ (by omega)

include hfg hJz hz in
/-- 有限自由加群を `a` 次に置いた単一複体：`λ(H^m(K(z; M[−a]))) = 0`（`m < a`）。 -/
lemma len_koszul_single (a m : ℤ) (hm : m < a) (M : ModuleCat.{u} C) [Module.Free C M]
    [Module.Finite C M] :
    lam.len ((koszulComplexOn z ((HomologicalComplex.single _ _ a).obj M)).homology m) = 0 := by
  let F := HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a ⋙ koszulFunctor z
  change lam.len ((F.obj M).homology m) = 0
  apply finiteFree_module_induction (fun N ↦ lam.len ((F.obj N).homology m) = 0) ?_ ?_ ?_ ?_ M
  · intro N hN
    exact len_koszul_isZero lam z ((HomologicalComplex.single _ _ a).map_isZero hN) m
  · exact len_koszul_single_ring lam z hz a m hm
  · intro N N' e hN
    let eh := (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) m).mapIso
      (F.mapIso e)
    exact (lam.len_congr _ _ eh.toLinearEquiv).symm.trans hN
  · intro N N' hN hN'
    let S : ShortComplex (ModuleCat.{u} C) :=
      ModuleCat.shortComplexOfCompEqZero (LinearMap.inl C N N') (LinearMap.snd C N N') (by ext; rfl)
    have hS : S.ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro y hy
        exact ⟨y.1, Prod.ext rfl hy.symm⟩
      · exact (ModuleCat.mono_iff_injective _).mpr (fun y z h ↦ congrArg Prod.fst h)
      · exact (ModuleCat.epi_iff_surjective _).mpr (fun y ↦ ⟨(0, y), rfl⟩)
    have := hS.mono_f
    have := hS.epi_g
    have hs := hS.map (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a)
    have hK := koszulFunctor_shortExact z _ hs
    exact lam.len_eq_zero_of_exact _ _
      (LinearMap.exact_iff.mpr (hK.homology_exact₂ m).moduleCat_range_eq_ker.symm)
      (isPowTorsion_koszul hfg z hJz _ m) (isPowTorsion_koszul hfg z hJz _ m)
      (isPowTorsion_koszul hfg z hJz _ m) hN hN'

include hfg hJz hz in
/-- **上からの評価**：有界有限自由複体 `Q` が `m` 次以下で零なら `λ(H^m(K(z; Q))) = 0`。 -/
theorem len_homology_koszulComplexOn_eq_zero (Q : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfree : ∀ i, Module.Free C (Q.X i)) (hfinite : ∀ i, Module.Finite C (Q.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i)) (m : ℤ)
    (hm : ∀ i, i ≤ m → IsZero (Q.X i)) :
    lam.len ((koszulComplexOn z Q).homology m) = 0 := by
  obtain ⟨a, b, hab⟩ := hbounded
  have hp (i : ℤ) : Module.Projective C (Q.X i) := by
    have := hfree i
    exact Module.Projective.of_free
  exact lambdaHomology_koszul_projective_amplitude lam hfg z hJz hz Q hfinite hp
    (m + 1) b (fun i hi ↦ hi.elim (fun h ↦ hm i (by omega))
      (fun h ↦ hab i (Or.inr h))) m (Or.inl (by omega))

end upper


end TorBound

/-! ## Lemma 5.3 の後半 -/

namespace ParamQuot

open TorBound

variable {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C) {h : ℕ} (x : Fin h → R)
  {J : Ideal C} (lam : NormalizedLength C J)

/-- `L` を消す `r` の冪は、`L` の射影分解の上で零ホモトピック。 -/
lemma exists_pow_kills_resolution (L : Type u) [AddCommGroup L] [Module R L]
    {d : ℕ} (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : IsResolutionOf P (ModuleCat.of R L))
    (hlen : ∀ i, i < -(d : ℤ) → IsZero (P.X i)) (r : R) (hr : ∀ l : L, r • l = 0) :
    ∃ w : ℕ, Nonempty (Homotopy (r ^ w • 𝟙 P) 0) := by
  refine exists_pow_nullHomotopy_of_homology_annihilated P r hP.projective
    ⟨-(d : ℤ), 0, fun i hi ↦ hi.elim (hlen i) (hP.isZero_X i)⟩ fun i ↦ ?_
  by_cases hi : i = 0
  · subst hi
    rw [← cancel_mono hP.homologyZeroIso.hom, zero_comp, Linear.smul_comp, Category.id_comp,
      ← Category.comp_id hP.homologyZeroIso.hom, ← Linear.comp_smul]
    convert comp_zero
    ext l
    exact hr l
  · exact (hP.isZero_homology i hi).eq_of_src _ _

/-- **Lemma 5.3 の後半**：`x_j L = 0`、`L` の長さ `d` 以下の有限自由分解、`J` は有限生成で
`J ⊆ √((x)C)`、Koszul ホモロジーの評価 `λ(H_q(x^v; C)) = 0`（`q, v > 0`）なら、
`i + h > d` で `λ(Tor_i^R(C, L)) = 0`。 -/
theorem len_torAlg_eq_zero (hfg : J.FG) (hJ : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (L : Type u) [AddCommGroup L] [Module R L] (hL : ∀ j (l : L), x j • l = 0)
    {d : ℕ} (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : IsResolutionOf P (ModuleCat.of R L))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (hlen : ∀ i, i < -(d : ℤ) → IsZero (P.X i)) (i : ℕ) (hi : d < i + h) :
    lam.len (TorAlg φ i L) = 0 := by
  let PC := baseChange φ P
  -- 各 `x_j` の冪が `P` 上で零ホモトピック。共通の冪 `w ≥ 1` をとる
  choose ws hws using fun j ↦ exists_pow_kills_resolution L P hP hlen (x j) (hL j)
  let w := Finset.univ.sup ws + 1
  have hw : 0 < w := Nat.succ_pos _
  have hkill : ∀ j, Kills (φ (x j) ^ w) PC := by
    intro j
    obtain ⟨H⟩ := hws j
    have hP' : (x j) ^ w • 𝟙 ((homotopyQuot R).obj P) = 0 :=
      pow_smul_id_eq_zero_of_le ((nonempty_homotopy_smul_id_zero_iff _ P).mp ⟨H⟩)
        ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))
    obtain ⟨H'⟩ := (nonempty_homotopy_smul_id_zero_iff _ P).mpr hP'
    have H'' := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H'
    have eq1 : φ (x j) ^ w • 𝟙 PC =
        ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (x j ^ w • 𝟙 P) := by
      rw [← map_pow]
      exact (baseChange_smulId φ P (x j ^ w)).symm
    refine (nonempty_homotopy_smul_id_zero_iff _ PC).mp
      ⟨(Homotopy.ofEq eq1).trans (H''.trans (Homotopy.ofEq (Functor.map_zero _ _ _)))⟩
  -- (Supp)：共通の冪だけを使う。零作用の錐では追加の冪は不要。
  let c : Fin h → C := fun k ↦ φ (x k) ^ w
  have hJc : J ≤ (Ideal.span (Set.range c)).radical :=
    le_radical_span_pow (φ ∘ x) hJ w
  have hz : ∀ q : ℕ, 0 < q → lam.len (koszulHomologySelf c q) = 0 := by
    have heq : c = fun k ↦ φ (x k ^ w) := by funext k; simp [c]
    rw [heq]
    exact hzero w hw
  have hperfect : strictlyPerfectComplex R P := by
    refine ⟨⟨-(d : ℤ), 0, ?_, ?_⟩, fun q ↦ ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      exact hlen
    · rw [CochainComplex.isStrictlyLE_iff]
      exact hP.isZero_X
    · have := hfree q
      exact ⟨hfin q, Module.Projective.of_free⟩
  -- (Kos_d) の確認と共通の反復錐定理により消滅する。
  rw [lam.len_congr _ _ (torIsoCochain φ hP i).toLinearEquiv]
  exact LengthAlgebra.lambdaHomology_projective_vanishing lam hfg c hJc hz PC
    (strictlyPerfectComplex_baseChange φ P hperfect)
    (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ PC).mpr (hkill j))
    (-(d : ℤ)) 0
    (fun q hq ↦ (ModuleCat.extendScalars φ).map_isZero
      (hq.elim (hlen q) (hP.isZero_X q))) (-(i : ℤ)) (Or.inl (by omega))

end ParamQuot


end SerrePositivity
