module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# スカラー倍がホモトピー圏で消えること

- 三角形の補題：完全三角形 `X → Y → Z → X[1]` で `(a • 𝟙 Y) ≫ g = 0` かつ
  `h ≫ (a • 𝟙 X)⟦1⟧' = 0` なら `(a * a) • 𝟙 Z = 0`。
- `a • 𝟙 P` が零ホモトピックであることは、ホモトピー圏で `a • 𝟙 = 0` であることと同じ。
- 写像錐：`a` が `X`、`Y` 上で零ホモトピックなら `a²` は `Cone(f)` 上で零ホモトピック。
  `Cone(c • 𝟙 X)` には `c²` が零ホモトピックに作用する。

後半では、有界射影複体の全ホモロジーを消すスカラーについて、
ある冪が複体上で零ホモトピックになることを次数に関する帰納法で証明する。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

/-! ## 完全三角形の補題 -/

section triangle

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [(shiftFunctor C (1 : ℤ)).Linear R]

/-- 完全三角形 `X → Y → Z → X[1]` で `a` が `g` の前と `h` の後ろで消えるなら、`a²` は `Z` 上で `0`。 -/
lemma smul_mul_self_id_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (a : R)
    (h₂ : (a • 𝟙 T.obj₂) ≫ T.mor₂ = 0)
    (h₃ : T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map (a • 𝟙 T.obj₁) = 0) :
    (a * a) • 𝟙 T.obj₃ = 0 := by
  set u : T.obj₃ ⟶ T.obj₃ := a • 𝟙 T.obj₃
  have hu₂ : T.mor₂ ≫ u = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← h₂, Linear.smul_comp, Category.id_comp]
  have hu₃ : u ≫ T.mor₃ = 0 := by
    rw [← h₃, Linear.smul_comp, Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
      Linear.comp_smul, Category.comp_id]
  obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ T hT u hu₂
  have : (a * a) • 𝟙 T.obj₃ = u ≫ u := by
    rw [mul_smul, Linear.smul_comp, Category.id_comp]
  rw [this]
  calc u ≫ u = u ≫ (T.mor₃ ≫ v) := by rw [← hv]
    _ = 0 := by rw [← Category.assoc, hu₃, zero_comp]

end triangle

variable {R : Type u} [CommRing R]

/-- ホモトピー圏 `K(R)` への商関手。 -/
noncomputable abbrev homotopyQuot (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient _ _

/-- `a • 𝟙 P` が零ホモトピックであることは、ホモトピー圏で `a • 𝟙 = 0` であることと同じ。 -/
lemma nonempty_homotopy_smul_id_zero_iff (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    Nonempty (Homotopy (a • 𝟙 P) 0) ↔ a • 𝟙 ((homotopyQuot R).obj P) = 0 := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff, Functor.map_smul, CategoryTheory.Functor.map_id]

/-- `a^v • 𝟙 = 0` なら `w ≥ v` で `a^w • 𝟙 = 0`。 -/
lemma pow_smul_id_eq_zero_of_le {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
    {a : R} {v w : ℕ} (h : a ^ v • 𝟙 X = 0) (hvw : v ≤ w) : a ^ w • 𝟙 X = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hvw
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

section cone

variable {X Y : CochainComplex (ModuleCat.{u} R) ℤ}

/-- `a` が `X`、`Y` 上で零ホモトピックなら、`a²` は `Cone(f)` 上で零ホモトピック。 -/
lemma mappingCone_smul_mul_self_eq_zero (f : X ⟶ Y) (a : R)
    (hX : a • 𝟙 ((homotopyQuot R).obj X) = 0) (hY : a • 𝟙 ((homotopyQuot R).obj Y) = 0) :
    (a * a) • 𝟙 ((homotopyQuot R).obj (CochainComplex.mappingCone f)) = 0 :=
  smul_mul_self_id_eq_zero _ (HomotopyCategory.mappingCone_triangleh_distinguished f) a
    (by
      have h : a • 𝟙 (CochainComplex.mappingCone.triangleh f).obj₂ = 0 := hY
      rw [h, zero_comp])
    (by
      have h : a • 𝟙 (CochainComplex.mappingCone.triangleh f).obj₁ = 0 := hX
      rw [h, Functor.map_zero, comp_zero])

/-- `Cone(c • 𝟙 X)` には `c²` が零ホモトピックに作用する。 -/
lemma mappingCone_smulId_mul_self_eq_zero (c : R) :
    (c * c) • 𝟙 ((homotopyQuot R).obj (CochainComplex.mappingCone (smulId c X))) = 0 := by
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished (smulId c X)
  set T := CochainComplex.mappingCone.triangleh (smulId c X)
  have h₂ : c • 𝟙 T.obj₂ = T.mor₁ := by
    change c • 𝟙 ((homotopyQuot R).obj X) = (homotopyQuot R).map (c • 𝟙 X)
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have h₁ : c • 𝟙 T.obj₁ = T.mor₁ := h₂
  refine smul_mul_self_id_eq_zero T hT c ?_ ?_
  · rw [h₂]
    exact comp_distTriang_mor_zero₁₂ _ hT
  · rw [h₁]
    exact comp_distTriang_mor_zero₃₁ _ hT

end cone

end SerrePositivity

end

/-!
## ホモロジーを消すスカラーの冪は零ホモトピック

射影加群からなる有界複体 `P` で、スカラー `r` がすべてのホモロジー `H^i(P)` を消すなら、
ある冪 `r^n • 𝟙 P` は零ホモトピック（`exists_pow_nullHomotopy_of_homology_annihilated`）。

証明は上の段から一つずつ消していく：`f : P ⟶ P` が `k` 次より上で零なら、`r • f` は `k` 次でも零な
射とホモトピックである（`clear_degree`。`f_k` はサイクルに落ち、`r` がホモロジーを消すので境界に
なり、射影性で `P^k → P^{k-1}` に持ち上がる）。幅の分だけ繰り返せば `r^n • 𝟙 P ∼ 0`。
局所化や Lemma 3.5 の入力は使わない。`PerfectComplex/Support.lean` で、ホモロジーの台から
台の条件 `IsSupported` を出すのに使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T]

set_option backward.isDefEq.respectTransparency.types false in
/-- `f : P ⟶ P` が `k` 次より上で零で、`r` が `H^k(P)` を消すなら、`r • f` は `k` 次以上で零な射と
ホモトピー圏で等しい。 -/
lemma clear_degree (P : CochainComplex (ModuleCat.{u} T) ℤ) (r : T) (k : ℤ)
    [Projective (P.X k)] (f : P ⟶ P)
    (hf : ∀ i, k < i → f.f i = 0)
    (hr : r • 𝟙 (P.homology k) = 0) :
    ∃ g : P ⟶ P, (∀ i, k ≤ i → g.f i = 0) ∧
      (homotopyQuot T).map g = r • (homotopyQuot T).map f := by
  classical
  let S := P.sc' (k - 1) k (k + 1)
  let e : P.homology k ≅ S.homology :=
    P.homologyIsoSc' (k - 1) k (k + 1)
      (by simp [CochainComplex.prev]) (by simp [CochainComplex.next])
  have hrS : r • 𝟙 S.homology = 0 := by
    have hzero (x : P.homology k) : r • x = 0 :=
      congrArg (fun q : P.homology k ⟶ P.homology k ↦ q.hom x) hr
    ext y
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    change r • e.toLinearEquiv x = 0
    rw [← e.toLinearEquiv.map_smul, hzero x, map_zero]
  have hcycle : f.f k ≫ S.g = 0 := by
    change f.f k ≫ P.d k (k + 1) = 0
    rw [f.comm k (k + 1), hf (k + 1) (by omega), comp_zero]
  let u := S.liftCycles (f.f k) hcycle
  let B := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hB : B.Exact := B.exact_of_g_is_cokernel S.homologyIsCokernel
  have hru : (r • u) ≫ S.homologyπ = 0 := by
    calc
      _ = (u ≫ S.homologyπ) ≫ (r • 𝟙 S.homology) := by
        simp [Linear.smul_comp, Linear.comp_smul]
      _ = 0 := by rw [hrS, comp_zero]
  let h := hB.liftFromProjective (r • u) hru
  have hh : h ≫ P.d (k - 1) k = r • f.f k := by
    change h ≫ S.f = r • f.f k
    rw [← S.toCycles_i, ← Category.assoc, hB.liftFromProjective_comp,
      Linear.smul_comp, S.liftCycles_i]
  let H : ∀ i j : ℤ, P.X i ⟶ P.X j := fun i j ↦
    if hi : i = k then
      if hj : j = k - 1 then
        eqToHom (congrArg P.X hi) ≫ h ≫ eqToHom (congrArg P.X hj.symm)
      else 0
    else 0
  let n := Homotopy.nullHomotopicMap H
  have hn : (homotopyQuot T).map n = 0 := by
    apply (HomotopyCategory.quotient_map_eq_zero_iff _).mpr
    refine ⟨Homotopy.nullHomotopy H ?_⟩
    intro i j hij
    dsimp [H]
    split_ifs with hi hj
    · exfalso
      apply hij
      change j + 1 = i
      omega
    all_goals rfl
  have hn_f (i : ℤ) : n.f i = P.d i (i + 1) ≫ H (i + 1) i + H i (i - 1) ≫ P.d (i - 1) i :=
    Homotopy.nullHomotopicMap_f (C := P) (D := P)
      (k₂ := i - 1) (k₁ := i) (k₀ := i + 1)
      (by change i - 1 + 1 = i; omega) rfl H
  refine ⟨r • f - n, ?_, ?_⟩
  · intro i hi
    change r • f.f i - n.f i = 0
    rw [hn_f]
    by_cases hik : i = k
    · subst i
      simp [H, hh, show k + 1 ≠ k by omega]
    · have hki : k < i := by omega
      simp [H, hf i hki, hik, show i + 1 ≠ k by omega]
  · rw [Functor.map_sub, Functor.map_smul, hn, sub_zero]

/-- **ホモロジーを消すスカラーの冪は零ホモトピック**：射影加群からなる有界複体 `P` で `r` が
すべてのホモロジーを消すなら、ある `n` で `r^n • 𝟙 P ∼ 0`。 -/
theorem exists_pow_nullHomotopy_of_homology_annihilated
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (r : T)
    (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hr : ∀ i, r • 𝟙 (P.homology i) = 0) :
    ∃ n : ℕ, Nonempty (Homotopy (r ^ n • 𝟙 P) 0) := by
  obtain ⟨a, b, hab⟩ := hbound
  have step : ∀ n : ℕ, ∃ f : P ⟶ P,
      (∀ i, b - (n : ℤ) < i → f.f i = 0) ∧
        (homotopyQuot T).map f = r ^ n • 𝟙 ((homotopyQuot T).obj P) := by
    intro n
    induction n with
    | zero =>
      refine ⟨𝟙 P, ?_, by simp⟩
      intro i hi
      exact (hab i (Or.inr (by simpa using hi))).eq_of_src _ _
    | succ n ih =>
      obtain ⟨f, hf, hclass⟩ := ih
      have := hproj (b - (n : ℤ))
      obtain ⟨g, hg, hgc⟩ := clear_degree P r (b - (n : ℤ)) f hf (hr _)
      refine ⟨g, fun i hi ↦ hg i (by push_cast at hi; omega), ?_⟩
      rw [hgc, hclass, ← mul_smul, ← pow_succ']
  obtain ⟨f, hf, hc⟩ := step (b - a + 1).toNat
  have hzero : f = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i < a
    · exact (hab i (Or.inl hi)).eq_of_src _ _
    · exact hf i (by omega)
  refine ⟨(b - a + 1).toNat, (nonempty_homotopy_smul_id_zero_iff _ P).mpr ?_⟩
  rw [← hc, hzero, Functor.map_zero]

end SerrePositivity

end
