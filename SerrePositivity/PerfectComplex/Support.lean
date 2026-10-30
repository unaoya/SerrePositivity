module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import SerrePositivity.HomologicalAlgebra.SupportNullHomotopy
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Support

/-!
# 台の条件の閉包性と Koszul 複体の台

## 概要

`Basic.lean` で定義した台の条件 `IsSupported z P`（ある `v` について、各 `j` で `z_j^v • 𝟙 P` が
零ホモトピック）が、ホモトピー同値・シフト・写像錐・基底変更・ひねりで保たれることを示し、
Koszul 複体 `K(x)` が `x` に台をもつことを示す。これらは、台つき完全複体の全体が `K₀` を定義するのに
十分な閉包性をもつこと（`Closure.lean`、`K0.lean`）の、「台」の部分である。

## 方針

台の条件はホモトピー圏 `K(R)` での等式 `z_j^v • 𝟙 P = 0` に言い換えられる（`isSupported_iff`）。
ホモトピー圏ではホモトピー同値は同型、写像錐は完全三角形の頂点なので、閉包性は `K(R)` が
`R` 線形な三角圏であることから従う。写像錐については `HomologicalAlgebra/NullHomotopy.lean` の
`mappingCone_smul_mul_self_eq_zero`（両端で `a • 𝟙 = 0` なら錐で `a² • 𝟙 = 0`）を使う。
基底変更とひねりは加法的関手で、ホモトピーを保ち、`z_j^v • 𝟙` を `φ(z_j)^v • 𝟙` に送ることによる。

## 内容

- 言い換え `isSupported_iff` と、各 `j` ごとの冪から共通の冪をとる `isSupported_of_forall`。
- ホモトピー同値・シフト・写像錐での閉包性。
- ホモロジーの零化：台をもつ複体のホモロジーは `(z)` の冪で消える
  （`IsSupported.le_radical_annihilator`）。ホモロジーの有限長性（`OrdinaryEuler.lean`）と
  冪ねじれ性（`NormalizedEuler.lean`）の根拠。
- Koszul 複体 `K(x)` は `x` に台をもつ（`isSupported_koszulComplex`）。
- 基底変更・ひねりでの閉包性。

後半の節では、ホモロジーの台で定義した条件 `HasHomologySupport` と `IsSupported` の関係を扱う。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 生成元を共通の正の冪で置き換えても根基による台の条件を保つ。 -/
lemma le_radical_span_pow {J : Ideal R} {e : ℕ} (z : Fin e → R)
    (hJ : J ≤ (Ideal.span (Set.range z)).radical) (v : ℕ) :
    J ≤ (Ideal.span (Set.range (fun j ↦ z j ^ v))).radical := by
  have h : Ideal.span (Set.range z) ≤
      (Ideal.span (Set.range (fun j ↦ z j ^ v))).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨v, Ideal.subset_span ⟨j, rfl⟩⟩
  exact hJ.trans (by simpa only [Ideal.radical_idem] using Ideal.radical_mono h)


/-- 台の条件のホモトピー圏での言い換え：`IsSupported z P` は、ある `v` について各 `j` で
ホモトピー圏 `K(R)` における等式 `z_j^v • 𝟙 P = 0` が成り立つことと同値。零ホモトピーの存在と
ホモトピー圏での等式の同値（`nonempty_homotopy_smul_id_zero_iff`）による。以下の閉包性は
この形で示す。 -/
lemma isSupported_iff {e : ℕ} (z : Fin e → R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsSupported z P ↔ ∃ v : ℕ, ∀ j, (z j) ^ v • 𝟙 ((homotopyQuot R).obj P) = 0 := by
  simp only [IsSupported, nonempty_homotopy_smul_id_zero_iff]

/-- 台の指数は正に取り直せる。 -/
lemma IsSupported.exists_pos {n : ℕ} {x : Fin n → R}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsSupported x P) :
    ∃ v : ℕ, 0 < v ∧ ∀ j, Nonempty (Homotopy (smulId (x j ^ v) P) 0) := by
  obtain ⟨v, hv⟩ := (isSupported_iff x P).mp hP
  refine ⟨v + 1, by omega, fun j ↦ ?_⟩
  exact (nonempty_homotopy_smul_id_zero_iff _ _).mpr
    (pow_smul_id_eq_zero_of_le (hv j) (by omega : v ≤ v + 1))


/-- 各 `j` ごとに冪 `v_j` があって `z_j^{v_j} • 𝟙 P = 0` なら、共通の冪 `v = max_j v_j` で
`IsSupported z P` が成り立つ。`z_j^v • 𝟙 = z_j^{v - v_j} • (z_j^{v_j} • 𝟙) = 0` だから
（`pow_smul_id_eq_zero_of_le`）。写像錐や Koszul 複体で、`j` ごとに別々の冪が出てくるときに使う。 -/
lemma isSupported_of_forall {e : ℕ} {z : Fin e → R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : ∀ j, ∃ v : ℕ, (z j) ^ v • 𝟙 ((homotopyQuot R).obj P) = 0) : IsSupported z P := by
  choose v hv using h
  rw [isSupported_iff]
  exact ⟨Finset.univ.sup v, fun j ↦
    pow_smul_id_eq_zero_of_le (hv j) (Finset.le_sup (Finset.mem_univ j))⟩

/-- ホモトピー圏での同型 `i : P ≅ Q` で台の条件は移る：`z_j^v • 𝟙 Q = i⁻¹ ≫ (z_j^v • 𝟙 P) ≫ i = 0`。 -/
lemma IsSupported.of_quotIso {e : ℕ} {z : Fin e → R} {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (i : (homotopyQuot R).obj P ≅ (homotopyQuot R).obj Q) (hP : IsSupported z P) :
    IsSupported z Q := by
  rw [isSupported_iff] at hP ⊢
  obtain ⟨v, hv⟩ := hP
  refine ⟨v, fun j ↦ ?_⟩
  have : (z j) ^ v • 𝟙 ((homotopyQuot R).obj Q) = i.inv ≫ ((z j) ^ v • 𝟙 _) ≫ i.hom := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]
  rw [this, hv j, zero_comp, comp_zero]

/-- ホモトピー同値 `P ≃ Q` で台の条件は移る（ホモトピー同値はホモトピー圏で同型だから）。 -/
lemma IsSupported.of_homotopyEquiv {e : ℕ} {z : Fin e → R}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (h : HomotopyEquiv P Q) (hP : IsSupported z P) :
    IsSupported z Q :=
  hP.of_quotIso (HomotopyCategory.isoOfHomotopyEquiv h)

/-- シフト `P⟦n⟧` で台の条件は保たれる。ホモトピー圏のシフト関手は線形なので、
`z_j^v • 𝟙 (P⟦n⟧)` は `(z_j^v • 𝟙 P)⟦n⟧ = 0` に、ホモトピー圏への射影とシフトの可換性
（`commShiftIso`）を通して一致する。 -/
lemma IsSupported.shift {e : ℕ} {z : Fin e → R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsSupported z P) (n : ℤ) : IsSupported z (P⟦n⟧) := by
  rw [isSupported_iff] at hP ⊢
  obtain ⟨v, hv⟩ := hP
  refine ⟨v, fun j ↦ ?_⟩
  let i := ((homotopyQuot R).commShiftIso n).app P
  have : (z j) ^ v • 𝟙 ((homotopyQuot R).obj (P⟦n⟧)) =
      i.hom ≫ (shiftFunctor _ n).map ((z j) ^ v • 𝟙 ((homotopyQuot R).obj P)) ≫ i.inv := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    simp
  rw [this, hv j, Functor.map_zero, zero_comp, comp_zero]

/-! ## 写像錐 -/

section cone

variable {X Y : CochainComplex (ModuleCat.{u} R) ℤ}

/-- `X`、`Y` が `z` に台をもてば、任意の射 `f : X ⟶ Y` の写像錐 `Cone f` も `z` に台をもつ。`X`、`Y` の
冪を `v`、`w` とし `u = max(v, w)` とすると、錐では `z_j^{2u} • 𝟙 = 0`
（`mappingCone_smul_mul_self_eq_zero`：両端で `a • 𝟙 = 0` なら錐で `a · a • 𝟙 = 0`）。 -/
lemma IsSupported.mappingCone {e : ℕ} {z : Fin e → R} (f : X ⟶ Y) (hX : IsSupported z X)
    (hY : IsSupported z Y) : IsSupported z (CochainComplex.mappingCone f) := by
  rw [isSupported_iff] at hX hY
  obtain ⟨v, hv⟩ := hX
  obtain ⟨w, hw⟩ := hY
  refine isSupported_of_forall fun j ↦ ⟨(v ⊔ w) + (v ⊔ w), ?_⟩
  rw [pow_add]
  exact mappingCone_smul_mul_self_eq_zero f _ (pow_smul_id_eq_zero_of_le (hv j) le_sup_left)
    (pow_smul_id_eq_zero_of_le (hw j) le_sup_right)

end cone

/-! ## ホモロジーの零化 -/

/-- `w` に台をもつ複体のホモロジーは `w` の冪で消える：`(w) ⊆ √(Ann H^i(P))`。零ホモトピックな射は
ホモロジーに零写像を誘導するので、`w_j^v • 𝟙 P ≃ 0` から `H^i(P)` 上で `w_j^v = 0`、すなわち
`w_j^v ∈ Ann H^i(P)`。ホモロジーが有限長であること（`OrdinaryEuler.lean`）と `(w)` 冪ねじれで
あること（`NormalizedEuler.lean`）の出発点。 -/
lemma IsSupported.le_radical_annihilator {e : ℕ} {w : Fin e → R}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsSupported w P) (i : ℤ) :
    Ideal.span (Set.range w) ≤ (Module.annihilator R (P.homology i)).radical := by
  obtain ⟨v, hv⟩ := hP
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨v, ?_⟩
  obtain ⟨H⟩ := hv j
  have h := H.homologyMap_eq i
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  rw [Module.mem_annihilator]
  intro x
  exact congrArg (fun f : P.homology i ⟶ P.homology i ↦ f.hom x) h

/-! ## Koszul 複体の台 -/

/-- 任意の複体 `P` を係数とする Koszul 複体 `K(x; P)` は `x` に台をもつ。`n` についての帰納法で、
`K(x; P) = Cone(x_n • 𝟙 K')`（`K' = K(x_0, …, x_{n-1}; P)`）とする。
最後の元 `x_n` については、`a • 𝟙` の錐では `a² • 𝟙 = 0`
（`mappingCone_smulId_mul_self_eq_zero`）。他の `x_j` については、帰納法の仮定で `K'` 上
`x_j^v • 𝟙 = 0` なので、錐で `x_j^{2v} • 𝟙 = 0`。各 `j` の冪を `isSupported_of_forall` でまとめる。
空列では `j` が存在しないので自明。 -/
theorem isSupported_koszulComplexOn : ∀ {n : ℕ} (x : Fin n → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ), IsSupported x (koszulComplexOn x P)
  | 0, x, _ => ⟨0, fun j ↦ j.elim0⟩
  | n + 1, x, P => by
    have ih := isSupported_koszulComplexOn (Fin.init x) P
    rw [isSupported_iff] at ih
    obtain ⟨v, hv⟩ := ih
    refine isSupported_of_forall fun j ↦ ?_
    change ∃ w : ℕ, (x j) ^ w • 𝟙 ((homotopyQuot R).obj
      (CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplexOn (Fin.init x) P)))) = 0
    induction j using Fin.lastCases with
    | last =>
      exact ⟨2, by rw [pow_two]; exact mappingCone_smulId_mul_self_eq_zero _⟩
    | cast j =>
      refine ⟨v + v, ?_⟩
      rw [pow_add]
      exact mappingCone_smul_mul_self_eq_zero _ _ (hv j) (hv j)

/-- 通常の Koszul 複体は、その定義列に台をもつ。係数複体を環の単一複体とした場合。 -/
theorem isSupported_koszulComplex {n : ℕ} (x : Fin n → R) :
    IsSupported x (koszulComplex x) := by
  rw [← koszulComplexOn_single]
  exact isSupported_koszulComplexOn _ _

/-! ## 基底変更とひねり -/

section baseChange

variable {A C : Type u} [CommRing A] [CommRing C]

/-- `P` が `z` に台をもてば、基底変更 `P ⊗_A C` は `φ ∘ z` に台をもつ。係数拡大関手はホモトピーを
保ち（`mapHomotopy`）、`z_j^v • 𝟙 P` を `φ(z_j)^v • 𝟙 (P ⊗_A C)` に送る
（`extendScalars_mapHomologicalComplex_smul`）から。 -/
lemma isSupported_baseChange (φ : A →+* C) {e : ℕ} {z : Fin e → A}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsSupported z P) :
    IsSupported (φ ∘ z) (baseChange φ P) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun j ↦ ?_⟩
  obtain ⟨H⟩ := hv j
  have := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H
  rw [extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero, map_pow] at this
  exact ⟨this⟩

end baseChange

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- 環準同型 `f : T → T` に沿った係数制限関手は、`f` で固定される元 `c` によるスカラー倍と両立する：
`restrictScalars f` した加群では `c • x` が `f(c) • x` なので、`f c = c` なら両者は一致する。 -/
lemma restrictScalars_mapHomologicalComplex_smul_of_fixed (f : T →+* T) (c : T) (hc : f c = c)
    {ι : Type*} {cs : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} T) cs} (u : K ⟶ L) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (c • u) =
      c • ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map u := by
  ext i x
  change c • (u.f i x) = f c • (u.f i x)
  rw [hc]

/-- `G` の `T` への作用が `A` 線形（`SMulCommClass G A T`）なら、`A` の元の像は固定される：
`g • (a • 1) = a • (g • 1) = a • 1`。 -/
lemma toRingHom_algebraMap (g : G) (a : A) :
    MulSemiringAction.toRingHom G T g (algebraMap A T a) = algebraMap A T a := by
  change g • algebraMap A T a = algebraMap A T a
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

/-- `A` の元の列 `z` から来る台はひねり `twist g` で保たれる。ひねりは `g` の作用に沿った係数制限で、
ホモトピーを保ち、`algebraMap A T (z_j)^v` は `g` で固定される（`toRingHom_algebraMap`）ので
`z_j^v • 𝟙` はそのまま `z_j^v • 𝟙` に移る。`§5.1` の `g^*P` が再び `K₀^{m}(T)` の元を定めること
（`Closure.lean`、`K0.lean`）に使う。 -/
lemma isSupported_twist {e : ℕ} (z : Fin e → A) (g : G) {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : IsSupported (algebraMap A T ∘ z) P) : IsSupported (algebraMap A T ∘ z) (twist g P) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun j ↦ ?_⟩
  obtain ⟨H⟩ := hv j
  have hfix : MulSemiringAction.toRingHom G T g ((algebraMap A T ∘ z) j ^ v) =
      (algebraMap A T ∘ z) j ^ v := by
    rw [map_pow, Function.comp_apply, toRingHom_algebraMap]
  have := (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomotopy H
  rw [restrictScalars_mapHomologicalComplex_smul_of_fixed _ _ hfix, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at this
  exact ⟨this⟩

end twist

end SerrePositivity

end

/-!
## ホモロジーの台と台の条件

論文では「`V(JT)` に台をもつ完全複体」をホモロジーの台で定義する：`HasHomologySupport I P` は、
各ホモロジー `H^i(P)` の台（`Module.support`、`Supp H^i(P) ⊆ Spec T`）が閉集合 `V(I)` に入ること。
一方 `Basic.lean` の `IsSupported w P` は零ホモトピーで定義した。この節は両者が有界な有限射影複体に
ついて一致することを示す（`isSupported_iff_homologySupport`）。

- `IsSupported w P → HasHomologySupport (w) P` は `IsSupported.le_radical_annihilator`。
- 逆：各次数で、有限生成な項からホモロジーに入る像は `w_j` のある冪で消える。
  射影性で境界へ持ち上げ、有界な複体の上の次数から順に零にする
  （`SupportNullHomotopy.lean` の `exists_pow_nullHomotopy_of_homology_support`）。
  ホモロジー自身の有限生成性や環の Noether 性は不要。
- Noether 環での、ホモロジー全体を消す共通の冪についての既存の補題も残す。

これで、ホモロジーの台で定義した条件から Lemma 3.5 の要求する `IsPerfectSupported` が得られる
（`isPerfectSupported_of_homologySupport`）。Lemma 5.2 で、`D'` 加群 `M` の分解 `P` の基底変更
`P ⊗ T` が `m_A` に台をもつことを言うのに使う（`IntersectionMultiplicity/ResolutionEvaluation.lean`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- 各ホモロジー `H^i(P)` の台 `Supp H^i(P) ⊆ Spec T` が閉集合 `V(I)` に入ること。論文の
「`V(I)` に台をもつ複体」の定義に当たる。 -/
def HasHomologySupport (I : Ideal T) (P : CochainComplex (ModuleCat.{u} T) ℤ) : Prop :=
  ∀ i, Module.support T (P.homology i) ⊆ PrimeSpectrum.zeroLocus I

section noetherian

variable [IsNoetherianRing T]

/-- 項が有限生成な複体では、`HasHomologySupport I P` は各 `i` で `I ⊆ √(Ann H^i(P))` と同値。
Noether 環上の有限生成加群 `M` の台は `V(Ann M)`（Mathlib の `Module.support_eq_zeroLocus`）で、
`V(J) ⊆ V(I)` は `I ⊆ √J` と同値だから。 -/
lemma homologySupport_iff_le_radical_annihilator (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i)) :
    HasHomologySupport I P ↔ ∀ i, I ≤ (Module.annihilator T (P.homology i)).radical := by
  unfold HasHomologySupport
  apply forall_congr'
  intro i
  have := hfinite i
  have := homology_moduleFinite P i
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]

/-- ホモロジーの台の条件から、各次数 `i` で `I` のある冪 `I^n` が `H^i(P)` を消す。`I ⊆ √(Ann H^i(P))`
と、Noether 環のイデアルが有限生成であることから（`IsPowTorsion.of_le_radical_annihilator`）。
冪 `n` は `i` によるので、共通の冪は次の補題でとる。 -/
lemma homology_pow_torsion_of_support (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i))
    (hP : HasHomologySupport I P) (i : ℤ) :
    ∃ n : ℕ, Module.IsTorsionBySet T (P.homology i) (I ^ n : Ideal T) :=
  IsPowTorsion.of_le_radical_annihilator I.fg_of_isNoetherianRing
    ((homologySupport_iff_le_radical_annihilator I P hfinite).mp hP i)

/-- 有界な複体では、すべてのホモロジーを消す共通の冪 `I^n` がとれる。ホモロジーが非零でありうる
次数は範囲 `[a, b]` の有限個なので、各次数の冪の最大値をとればよい。範囲の外ではホモロジーが零で
何も消す必要がない。 -/
theorem exists_common_pow_annihilator_of_homologySupport (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport I P) :
    ∃ n : ℕ, ∀ i, Module.IsTorsionBySet T (P.homology i) (I ^ n : Ideal T) := by
  classical
  obtain ⟨a, b, hab⟩ := hbounded
  choose n hn using homology_pow_torsion_of_support I P hfinite hP
  refine ⟨(Finset.Icc a b).sup n, fun i ↦ ?_⟩
  by_cases hi : i ∈ Finset.Icc a b
  · have hpow : I ^ (Finset.Icc a b).sup n ≤ I ^ n i :=
      Ideal.pow_le_pow_right (Finset.le_sup hi)
    intro x r
    exact @hn i x ⟨r, hpow r.property⟩
  · have hz : IsZero (P.homology i) :=
      isZero_homology_of_isZero_X _ _ (hab i (by simp only [Finset.mem_Icc] at hi; omega))
    have := ModuleCat.subsingleton_of_isZero hz
    intro x r
    exact Subsingleton.elim _ _

end noetherian

/-! ## 任意の可換環における台の条件との関係 -/

/-- スカラーの冪の零ホモトピーはホモロジーの幾何学的支持を制限する。
この向きには有界性・有限生成性・射影性も不要。 -/
lemma IsSupported.homologySupport {e : ℕ} {w : Fin e → T}
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsSupported w P) :
    HasHomologySupport (Ideal.span (Set.range w)) P := by
  intro i p hp r hr
  obtain ⟨n, hn⟩ := hP.le_radical_annihilator i hr
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance n
    (Module.annihilator_le_of_mem_support hp hn)

/-- 有界で各項が有限生成射影的な複体では、ホモロジーの台の条件 `HasHomologySupport (w) P` から
台の条件 `IsSupported w P` が出る。各生成元について有限な像を冪で消去して零ホモトピーを作り、
`isSupported_of_forall` で共通の冪をとる。Noether 性は仮定しない。 -/
theorem isSupported_of_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport (Ideal.span (Set.range w)) P) : IsSupported w P := by
  apply isSupported_of_forall
  intro j
  have hr : ∀ i, Module.support T (P.homology i) ⊆ PrimeSpectrum.zeroLocus {w j} :=
    fun i ↦ (hP i).trans (PrimeSpectrum.zeroLocus_anti_mono
      (Set.singleton_subset_iff.mpr (Ideal.subset_span (Set.mem_range_self j))))
  obtain ⟨v, hv⟩ := exists_pow_nullHomotopy_of_homology_support P (w j) hfinite hproj hbound hr
  exact ⟨v, (nonempty_homotopy_smul_id_zero_iff _ _).mp hv⟩

/-- 有界で各項が有限生成射影的な複体では、零ホモトピーによる台の条件 `IsSupported w P` と
ホモロジーの台による条件 `HasHomologySupport (w) P` は同値である。順方向は
`IsSupported.le_radical_annihilator`、逆方向は `isSupported_of_homologySupport`。 -/
theorem isSupported_iff_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    IsSupported w P ↔ HasHomologySupport (Ideal.span (Set.range w)) P := by
  constructor
  · exact IsSupported.homologySupport
  · exact isSupported_of_homologySupport w P hfinite hproj hbound

/-- 有界で各項が有限自由な複体で、ホモロジーの台が `V(w)` に入るものは、`w` に台をもつ完全複体
`IsPerfectSupported w P` である（自由加群は射影的なので `isSupported_of_homologySupport` が使える）。
論文の意味で「`V(w)` に台をもつ完全複体」であるものを、このプロジェクトの `PerfSupp T w` の元に
するための橋渡し。 -/
theorem isPerfectSupported_of_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hfree : ∀ i, Module.Free T (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport (Ideal.span (Set.range w)) P) : IsPerfectSupported w P where
  bounded := hbound
  free := hfree
  finite := hfinite
  supported := isSupported_of_homologySupport w P hfinite
    (fun i ↦ projective_of_free (hfree i)) hbound hP

end SerrePositivity

end
