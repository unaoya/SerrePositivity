module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# スカラー倍がホモトピー圏で消えること

## 概要

複体 `P` とスカラー `a` について「`a • 𝟙 P` が零ホモトピックである」という条件を扱う。
これは台つき完全複体の台の条件 `IsSupported`（`PerfectComplex/Basic.lean`：`z_j^v • 𝟙 P` が
零ホモトピック）の中身であり、このファイルはその条件を調べる道具をまとめる。前半は
完全三角形を使って条件が写像錐で保たれることを示し、後半はホモロジーについての弱い条件から
この条件を導く。

## 前半：完全三角形とスカラー倍

`a • 𝟙 P` が零ホモトピックであることは、ホモトピー圏 `K(R)` で `a • 𝟙 P = 0` であることと同じ
（`nonempty_homotopy_smul_id_zero_iff`）。そこでホモトピー圏の三角圏構造が使える。基本になるのは
次の補題である（`smul_mul_self_id_eq_zero`）：完全三角形 `X →f Y →g Z →h X[1]` で、`a • 𝟙 Y` が
`g` の前で消え、`a • 𝟙 X` が `h` の後ろで消えるなら、`a² • 𝟙 Z = 0`。証明は、`a • 𝟙 Z` は `g` と
合成して零なので `h` を経由する（完全三角形の性質）、そこでもう一度 `a` を掛けると `h` の後ろで
消える、というもの。指数が `a` から `a²` に上がる点が大事で、「台の条件は写像錐で保たれるが、
冪は増えてよい」という形で台つき完全複体の閉包性（`PerfectComplex/Support.lean`）に現れる。

- `mappingCone_smul_mul_self_eq_zero`：`a` が `X`、`Y` 上で零ホモトピックなら、`a²` は `Cone(f)` 上で
  零ホモトピック。
- `mappingCone_smulId_mul_self_eq_zero`：特に `Cone(c • 𝟙 X)` 上では `c²` が零ホモトピック。
  Koszul 複体 `K(x)` が `x` に台をもつことの帰納段になる。
- `pow_smul_id_eq_zero_of_le`：冪は大きくしてよい（`a^v • 𝟙 = 0` なら `w ≥ v` で `a^w • 𝟙 = 0`）。
  複数の生成元について共通の冪をとるときに使う。

後半（ホモロジーを消すスカラーの冪が零ホモトピックになること）は、下の節の冒頭で説明する。
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

/-- 完全三角形 `T = (X →f Y →g Z →h X[1])` とスカラー `a` について、`a • 𝟙 Y` のあとに `g` を
合成すると零（`h₂`）、`h` のあとに `(a • 𝟙 X)[1]` を合成すると零（`h₃`）なら、`a² • 𝟙 Z = 0`。

`u := a • 𝟙 Z` とおくと、仮定は `g ≫ u = 0` と `u ≫ h = 0` に言い換えられる。完全三角形では
`g ≫ u = 0` となる射 `u` は `h` を経由する、すなわち `u = h ≫ v` となる `v : X[1] ⟶ Z` がある
（Mathlib の `Triangle.yoneda_exact₃`）。すると `u ≫ u = u ≫ h ≫ v = 0 ≫ v = 0` である。
`a² • 𝟙 Z = u ≫ u` なので結論が従う。`R` 線形な一般の三角圏で成り立つ。 -/
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

/-- 複体の圏からホモトピー圏 `K(R)` への商関手。鎖写像をそのホモトピー類に送る。零ホモトピーの
条件をホモトピー圏の等式に言い換えるときの基準になるので、以下では一貫してこの名前で参照する。 -/
noncomputable abbrev homotopyQuot (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient _ _

/-- `a • 𝟙 P` が零ホモトピックであること（ホモトピー `Homotopy (a • 𝟙 P) 0` が存在すること）は、
ホモトピー圏で `a • 𝟙 P = 0` であることと同値である。Mathlib の `quotient_map_eq_zero_iff`
（商関手で零になる ⇔ 零ホモトピック）と、商関手がスカラー倍と恒等射を保つことによる。
台の条件 `IsSupported` をホモトピー圏で扱うための言い換え（`PerfectComplex/Support.lean` の
`isSupported_iff`）。 -/
lemma nonempty_homotopy_smul_id_zero_iff (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    Nonempty (Homotopy (a • 𝟙 P) 0) ↔ a • 𝟙 ((homotopyQuot R).obj P) = 0 := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff, Functor.map_smul, CategoryTheory.Functor.map_id]

/-- `a^v • 𝟙 X = 0` なら、`v ≤ w` となるすべての `w` で `a^w • 𝟙 X = 0`。`a^w = a^{w-v} · a^v` と
分けるだけ。複数の生成元 `z_j` についてそれぞれ冪 `v_j` がとれたとき、それらの最大値を共通の冪に
とるのに使う（`PerfectComplex/Support.lean` の `isSupported_of_forall`）。 -/
lemma pow_smul_id_eq_zero_of_le {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
    {a : R} {v w : ℕ} (h : a ^ v • 𝟙 X = 0) (hvw : v ≤ w) : a ^ w • 𝟙 X = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hvw
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

section cone

variable {X Y : CochainComplex (ModuleCat.{u} R) ℤ}

/-- `a` が `X`、`Y` 上でホモトピー圏で消えるなら、`a²` は写像錐 `Cone(f)` 上で消える。
写像錐の三角形 `X → Y → Cone(f) → X[1]` が完全三角形であることと `smul_mul_self_id_eq_zero` による
（`a • 𝟙 Y = 0` なら `g` の前で消え、`a • 𝟙 X = 0` なら `h` の後ろで消える）。台の条件が写像錐で
保たれること（`PerfectComplex/Support.lean` の `IsSupported.mappingCone`）の中身である。 -/
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

/-- `c • 𝟙 X` の写像錐 `Cone(c • 𝟙 X)` の上では、`c²` がホモトピー圏で消える。三角形
`X →(c • 𝟙) X → Cone → X[1]` において `c • 𝟙 X` は三角形の第一の射そのものなので、完全三角形で
隣り合う射の合成が零であること（`comp_distTriang_mor_zero₁₂`、`_₃₁`）から
`smul_mul_self_id_eq_zero` の二つの仮定が出る。Koszul 複体 `K(x) = Cone(x_n • 𝟙 K(x'))` が `x` に
台をもつことの帰納段（`PerfectComplex/Support.lean` の `isSupported_koszulComplex`）で、新しく
加わった元 `x_n` についての冪を与える。 -/
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
ある冪 `r^n • 𝟙 P` は零ホモトピックである（`exists_pow_nullHomotopy_of_homology_annihilated`）。
これは前半とは逆向きの主張で、「ホモロジーが `r` で消える」という弱い条件から「複体そのものが
`r` の冪で消える」という強い条件（台の条件 `IsSupported`）を導く。`r • 𝟙 P` 自身は一般には
零ホモトピックではなく、冪をとる必要がある。冪 `n` は複体の幅（非零の項のある次数の個数）で
抑えられる。

証明は上の次数から一段ずつ消していく帰納法である。鍵は `clear_degree`：`f : P ⟶ P` が `k` 次より
上で零なら、`r • f` は `k` 次以上で零な射とホモトピックである。実際 `f` は `k+1` 次で零なので
`f_k` は `P^k → P^{k+1}` と合成して消え、サイクルに値をとる。`r` が `H^k(P)` を消すので `r • f_k`
のホモロジー類は零、すなわち境界 `P^{k-1} → P^k` の像に入り、`P^k` が射影的なので
`h : P^k → P^{k-1}` に持ち上がる。この `h` を `k` 次だけの成分とするホモトピーで `r • f` から
`k` 次の成分を消せる。`𝟙 P` から始めて複体の幅の回数だけ繰り返せば、`r^n • 𝟙 P` は零射と
ホモトピックになる。局所化や Lemma 3.5 の入力は使わない。

`PerfectComplex/Support.lean` で、ホモロジーの台の条件 `HasHomologySupport` から台の条件
`IsSupported` を出すのに使う（`isSupported_of_homologySupport`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- 境界への因子分解があれば、一段の成分をホモトピーで消去できる。
射影性やホモロジーの消去条件は、因子分解を構成する側でのみ必要となる。 -/
lemma clear_degree_of_factorization (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (r : T) (k : ℤ) (f : P ⟶ P) (hf : ∀ i, k < i → f.f i = 0)
    (h : P.X k ⟶ P.X (k - 1)) (hh : h ≫ P.d (k - 1) k = r • f.f k) :
    ∃ g : P ⟶ P, (∀ i, k ≤ i → g.f i = 0) ∧
      (homotopyQuot T).map g = r • (homotopyQuot T).map f := by
  classical
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

set_option backward.isDefEq.respectTransparency.types false in
/-- 一段消去の補題。`P^k` が射影的で、`f : P ⟶ P` が `k` 次より上で零（`hf`）、`r` が `H^k(P)` を
零化する（`hr`）とき、`k` 次以上で零な `g : P ⟶ P` があって、ホモトピー圏で `g = r • f` となる。

証明の筋道：`f` は `k+1` 次で零なので `f_k` は `P^k → P^{k+1}` と合成して消え、サイクルへの射
`u : P^k → Z^k` を定める（`liftCycles`）。`r • u` はホモロジー `H^k = Z^k / B^k` で零なので境界
`B^k` に入り、`P^k` の射影性で `h : P^k → P^{k-1}` に持ち上がって `h ≫ d = r • f_k` となる
（`liftFromProjective`）。`h` を `(k, k-1)` 成分だけにもつホモトピーから零ホモトピックな射
`n := nullHomotopicMap H` を作り、`g := r • f - n` とおく。`k` 次では `r • f_k - h ≫ d = 0`、
`k` 次より上では `f` も `n` も零なので `g` は `k` 次以上で零であり、`n` が零ホモトピックなので
ホモトピー圏では `g = r • f` である。 -/
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
  exact clear_degree_of_factorization P r k f hf h hh

/-- **ホモロジーを消すスカラーの冪は零ホモトピック**。各項が射影的で、`a` 次から `b` 次の範囲に
乗る複体 `P` について、`r` がすべてのホモロジー `H^i(P)` を零化するなら、`r^n • 𝟙 P` が
零ホモトピックになる `n` がある（証明では `n = b - a + 1`）。

`𝟙 P` から始めて `clear_degree` を `b` 次、`b - 1` 次、…と順に適用すると、`k` 回目のあとには
「`b - k` 次より上で零で、ホモトピー圏で `r^k • 𝟙 P` に等しい」射が得られる（`step`）。
`k = b - a + 1` まで進めると `a` 次より下でも零なので射は零になり、`r^n • 𝟙 P` はホモトピー圏で
`0`、すなわち零ホモトピックである。 -/
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
