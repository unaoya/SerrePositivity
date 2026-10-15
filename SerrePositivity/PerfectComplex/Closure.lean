module

public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.HomologicalAlgebra.Basic
public import SerrePositivity.HomologicalAlgebra.FiniteFreeBaseChange
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# 台つき完全複体の閉包性

## 概要

`IsPerfectSupported z P`（有界・各項が有限自由・`z` に台をもつ。`Basic.lean`）が、複体の同型・
写像錐・シフト・零複体・基底変更・ひねりで保たれることを示す。`K₀` を定義する（`K0.lean`）には、
関係式に現れる写像錐が再び台つき完全複体であることが要るし、基底変更 `K₀(A) → K₀(C)` や
ひねり `g^*` を `K₀` に作用させるには、それらが台つき完全複体を保つことが要る。Koszul 複体 `K(x)` が
`x` に台をもつ完全複体であること（`isPerfectSupported_koszulComplex`、`koszulPerfSupp`）もここで示す。

## 方針

三つの条件を別々に確かめる。有界性は各構成での項の形から、各項の有限自由性は
`HomologicalAlgebra/Basic.lean`（写像錐の項は直和）と、基底変更がテンソル積・ひねりが係数制限で
あることから、台の条件は `Support.lean` から。

## 内容

- 同型・写像錐・シフト・零複体（`IsPerfectSupported.of_iso`、`.mappingCone`、`.shift`、
  `isPerfectSupported_of_isZero`）。
- 基底変更 `baseChange φ`（`isPerfectSupported_baseChange`）。テンソル積 `C ⊗_A -` は有限自由加群を
  有限自由加群に送る。
- ひねり `twist g`（`isPerfectSupported_twist`）。`twist g P` の各項は `P` の項と同じ台集合で、`T` の
  作用を `g` でひねったものなので、恒等写像が `g⁻¹` 半線形同型になる（`twistSemilinearEquiv`）。
  これで自由性・有限性を移す。
- Koszul 複体。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R] {e : ℕ} {z : Fin e → R}

/-! ## 同型・写像錐・シフト・零複体 -/

/-- 複体の同型 `i : P ≅ P'` で台つき完全複体の条件は移る。各項の同型で有界性・有限自由性を移し、
台の条件は零ホモトピーを `i⁻¹ ≫ - ≫ i` で共役する。 -/
lemma IsPerfectSupported.of_iso {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (i : P ≅ P')
    (h : IsPerfectSupported z P) : IsPerfectSupported z P' where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦ (HomologicalComplex.Hom.isoApp i n).isZero_iff.mp (hab n hn)⟩
  free n := by
    have := h.free n
    exact Module.Free.of_equiv (HomologicalComplex.Hom.isoApp i n).toLinearEquiv
  finite n := by
    have := h.finite n
    exact Module.Finite.equiv (HomologicalComplex.Hom.isoApp i n).toLinearEquiv
  supported := by
    obtain ⟨v, hv⟩ := h.supported
    refine ⟨v, fun j ↦ ?_⟩
    obtain ⟨H⟩ := hv j
    refine ⟨(Homotopy.ofEq ?_).trans (((H.compRight i.hom).compLeft i.inv).trans
      (Homotopy.ofEq ?_))⟩
    · rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
    · simp

/-- 台つき完全複体の間の射 `f : X ⟶ Y` の写像錐は台つき完全複体。錐の項は `Cone^i = X^{i+1} ⊕ Y^i`
なので、`X` が `[a, b]`、`Y` が `[c, d]` に乗れば錐は `[min(a-1, c), max(b, d)]` に乗り、各項は
有限自由加群の直和で有限自由（`mappingCone_free_finite`）。台の条件は `IsSupported.mappingCone`。
`K₀` の錐の関係式（`K0.lean`）に現れる錐が `PerfSupp` の元であることの根拠。 -/
lemma IsPerfectSupported.mappingCone {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y)
    (hX : IsPerfectSupported z X) (hY : IsPerfectSupported z Y) :
    IsPerfectSupported z (CochainComplex.mappingCone f) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hX.bounded
    obtain ⟨c, d, hcd⟩ := hY.bounded
    refine ⟨min (a - 1) c, max b d, fun i hi ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · apply hab
      rcases hi with hi | hi
      · left; omega
      · right; omega
    · apply hcd
      rcases hi with hi | hi
      · left; omega
      · right; omega
  free i := by
    have := hX.free (i + 1); have := hY.free i
    have := hX.finite (i + 1); have := hY.finite i
    exact (mappingCone_free_finite f i).1
  finite i := by
    have := hX.free (i + 1); have := hY.free i
    have := hX.finite (i + 1); have := hY.finite i
    exact (mappingCone_free_finite f i).2
  supported := hX.supported.mappingCone f hY.supported

/-- 台つき完全複体のシフト `P⟦n⟧`（`(P⟦n⟧)^i = P^{i+n}`）は台つき完全複体。 -/
lemma IsPerfectSupported.shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsPerfectSupported z P) (n : ℤ) : IsPerfectSupported z (P⟦n⟧) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hP.bounded
    exact ⟨a - n, b - n, fun i hi ↦ hab (i + n) (by omega)⟩
  free i := hP.free (i + n)
  finite i := hP.finite (i + n)
  supported := hP.supported.shift n

/-- 零複体は（どんな `z` についても）台つき完全複体。各項が零なので有界・有限自由は自明で、
台の条件は `v = 0` でよい（零複体上の射はすべて零）。 -/
lemma isPerfectSupported_of_isZero {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsZero P) :
    IsPerfectSupported z P where
  bounded := ⟨0, 0, fun i _ ↦ (HomologicalComplex.eval _ _ i).map_isZero hP⟩
  free i := isZero_moduleCat_free ((HomologicalComplex.eval _ _ i).map_isZero hP)
  finite i := isZero_moduleCat_finite ((HomologicalComplex.eval _ _ i).map_isZero hP)
  supported := ⟨0, fun _ ↦ ⟨Homotopy.ofEq (hP.eq_of_src _ _)⟩⟩

/-! ## 基底変更 -/

section baseChange

variable {A C : Type u} [CommRing A] [CommRing C]

/-- `z` に台をもつ完全 `A` 複体 `P` の基底変更 `P ⊗_A C` は、`φ ∘ z` に台をもつ完全 `C` 複体。
係数拡大は零加群を零加群に送り（有界性）、有限自由加群を有限自由加群に送り、台の条件を保つ
（`isSupported_baseChange`）。論文 (3.6) の `K_0^{m}(A) → K_0^{m}(T)` を定義する根拠。 -/
lemma isPerfectSupported_baseChange (φ : A →+* C) {e : ℕ} {z : Fin e → A}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsPerfectSupported z P) :
    IsPerfectSupported (φ ∘ z) (baseChange φ P) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦ (ModuleCat.extendScalars.{u, u, u} φ).map_isZero (hab n hn)⟩
  free n := by
    have := h.free n
    exact free_baseChange φ (P.X n)
  finite n := by
    have := h.finite n
    exact finite_baseChange φ (P.X n)
  supported := isSupported_baseChange φ h.supported

end baseChange

/-! ## ひねり -/

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- `g⁻¹` の `T` への作用を環同型 `T ≃+* T` とみたもの。`twist g P` の各項への恒等写像が、この
環同型に沿った半線形写像になる（`twistSemilinearEquiv`）。 -/
noncomputable abbrev twistInvEquiv (g : G) : T ≃+* T := MulSemiringAction.toRingEquiv G T g⁻¹

/-- Mathlib の半線形同値 `M ≃ₛₗ[σ] N` は、`σ` とその逆が互いに逆であることを
`RingHomInvPair` インスタンスで要求する。`twistInvEquiv g` とその逆について登録しておく。 -/
instance (g : G) : RingHomInvPair (twistInvEquiv (T := T) g).toRingHom
    (twistInvEquiv (T := T) g).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (twistInvEquiv (T := T) g)

/-- 上のインスタンスの逆向き。 -/
instance (g : G) : RingHomInvPair (twistInvEquiv (T := T) g).symm.toRingHom
    (twistInvEquiv (T := T) g).toRingHom :=
  RingHomInvPair.symm _ _

/-- ひねり `g^*M`（`restrictScalars (g •)` した `M`。台集合は同じで、作用は `t •' x = (g • t) • x`）
への恒等写像 `x ↦ x` は、環同型 `g⁻¹ • : T ≃+* T` に沿った半線形同型である：
`t •' x = (g • (g⁻¹ • t)) •' x`、すなわち `φ(t • x) = (g⁻¹ • t) •' φ(x)`。半線形同型で自由性・
有限生成性が移るので、ひねりがこれらを保つことが従う。 -/
noncomputable def twistSemilinearEquiv (g : G) (M : ModuleCat.{u} T) :
    M ≃ₛₗ[(twistInvEquiv (T := T) g).toRingHom]
      (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' t x := by
    change t • x = (g • (g⁻¹ • t)) • x
    rw [smul_inv_smul]
  left_inv _ := rfl
  right_inv _ := rfl

/-- ひねり `g^*M` は、`M` が自由なら自由（`twistSemilinearEquiv` と、半線形同型で自由性が移ること）。 -/
lemma free_twist (g : G) (M : ModuleCat.{u} T) [Module.Free T M] :
    Module.Free T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) :=
  Module.Free.of_equiv (twistSemilinearEquiv g M)

/-- ひねり `g^*M` は、`M` が有限生成なら有限生成（半線形全射の像だから）。 -/
lemma finite_twist (g : G) (M : ModuleCat.{u} T) [Module.Finite T M] :
    Module.Finite T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) :=
  Module.Finite.of_surjective (twistSemilinearEquiv g M).toLinearMap
    (twistSemilinearEquiv g M).surjective

/-- `G` が `T` に `A` 線形に作用するとき、`A` の元の列 `z` から来る台をもつ完全 `T` 複体 `P` の
ひねり `g^*P` は、同じ `z` に台をもつ完全複体。項は台集合が同じなので有界性はそのまま、有限自由性は
`free_twist`・`finite_twist`、台の条件は `isSupported_twist`。§5.1 の `G` の `K₀^{m}(T)` への作用
（`K0.lean` の `twistHom`）の根拠。 -/
lemma isPerfectSupported_twist {e : ℕ} (z : Fin e → A) (g : G)
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (h : IsPerfectSupported (algebraMap A T ∘ z) P) :
    IsPerfectSupported (algebraMap A T ∘ z) (twist g P) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦
      (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).map_isZero (hab n hn)⟩
  free n := by
    have := h.free n
    exact free_twist g (P.X n)
  finite n := by
    have := h.finite n
    exact finite_twist g (P.X n)
  supported := isSupported_twist z g h.supported

end twist

/-! ## Koszul 複体は台つき完全複体 -/

/-- Koszul 複体 `K(x)` は `x` に台をもつ完全複体：`[-n, 0]` に乗り、各項は有限自由
（`CommutativeAlgebra/Koszul.lean`）、`x` に台をもつ（`isSupported_koszulComplex`）。 -/
theorem isPerfectSupported_koszulComplex {n : ℕ} (x : Fin n → R) :
    IsPerfectSupported x (koszulComplex x) where
  bounded := ⟨-(n : ℤ), 0, fun i hi ↦ by
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt x i hi
    · exact koszulComplex_isZero_X_of_pos x i hi⟩
  free i := (koszulComplex_free_finite_X x i).1
  finite i := (koszulComplex_free_finite_X x i).2
  supported := isSupported_koszulComplex x

/-- Koszul 複体を `PerfSupp R x`（`x` に台をもつ完全複体の型）の元として包んだもの。その類
`K0.mk (koszulPerfSupp x)` が `K₀^{(x)}` を生成する（`KoszulGeneration.lean`）。 -/
noncomputable def koszulPerfSupp {n : ℕ} (x : Fin n → R) : PerfSupp R x :=
  ⟨koszulComplex x, isPerfectSupported_koszulComplex x⟩

end SerrePositivity
