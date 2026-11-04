module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel

/-! # 一つの座標の完備化の反復

## 概要

一つの座標の H⁰ を二度当てた環 `IteratedCompletionH0` とその標準写像を作り、両方の座標について完備な加群への反映であること（`iteratedCompletion_isCompleteModuleReflection`）を示す。二つの座標の完備化 `PairCompletionH0` はこの反映として定義する（`Pair/Koszul`）。

## 方針

一つ目の座標の反映 `S` について、その座標で完備な加群には単位候補の延長から `S` の作用が入る（`IsCompleteModuleReflection.actionEquiv`）。完備な加群の間の線形写像はこの作用を保つので、反復した H⁰ からの `R` 線形写像は `S` 線形になり、二度目の反映の普遍性に帰着する。

## 規約

`pairKoszulCoordinates` は BhattScholze が使うので名前と定義を変えない。旧 `IteratedKoszulRing`。2b の B4 の後は二つの座標の Koszul 塔の行列模型（旧 `Pair/Tower`・`PairKoszul{Stage, Transition, Comparison, Product, Cone, Unit}`）を使わない（refactor-plan §3.5.3）。

## 使われ方

`Pair/Koszul`（`PairCompletionH0` の定義と比較）。
-/

@[expose] public noncomputable section

universe u

section IteratedKoszulRingPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- fの一座標完備化のH⁰を、dの標準像について再び完備化したH⁰。 -/
abbrev IteratedCompletionH0 (f d : R) :=
  letI := principalCompletionCommRing R f
  PrincipalCompletionH0 (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d)

/-- 反復したH⁰の可換環構造。 -/
@[instance_reducible] def iteratedCompletionCommRing (f d : R) :
    CommRing (IteratedCompletionH0 R f d) :=
  letI := principalCompletionCommRing R f
  principalCompletionCommRing (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d)

/-- 反復したH⁰への標準環準同型。 -/
def iteratedCompletionUnitRingHom (f d : R) :
    letI := iteratedCompletionCommRing R f d; R →+* IteratedCompletionH0 R f d :=
  letI := principalCompletionCommRing R f
  (principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)).comp (principalCompletionUnitRingHom R f)

/-- 反復したH⁰のR代数構造は、一座標の元の加群作用を制限したもの。 -/
@[instance_reducible] def iteratedCompletionAlgebra (f d : R) :
    letI := iteratedCompletionCommRing R f d; Algebra R (IteratedCompletionH0 R f d) := by
  letI := principalCompletionCommRing R f
  letI := principalCompletionAlgebra R f
  letI := iteratedCompletionCommRing R f d
  letI := principalCompletionAlgebra (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)
  letI : Module R (IteratedCompletionH0 R f d) :=
    Module.compHom (IteratedCompletionH0 R f d) (principalCompletionUnitRingHom R f)
  exact Algebra.ofModule
    (fun r x y ↦ by
      change ((principalCompletionUnitRingHom R f r) • x) * y =
        (principalCompletionUnitRingHom R f r) • (x * y)
      exact smul_mul_assoc _ _ _)
    (fun r x y ↦ by
      change x * ((principalCompletionUnitRingHom R f r) • y) =
        (principalCompletionUnitRingHom R f r) • (x * y)
      exact mul_smul_comm _ _ _)

/-- 反復した代数の標準写像は、二つの既存H⁰標準写像の合成。 -/
theorem iteratedCompletion_algebraMap (f d r : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    algebraMap R (IteratedCompletionH0 R f d) r = iteratedCompletionUnitRingHom R f d r := by
  rfl

/-- 二度目の主元完備化は、最初の元fについての導来完備性を保つ。 -/
theorem iteratedCompletion_isModuleComplete_first (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    IsModuleComplete R f (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  let := iteratedCompletionAlgebra R f d
  exact principalCompletionH0_isModuleComplete_of_other R (PrincipalCompletionH0 R f) f
    (principalCompletionUnitRingHom R f d) (principalCompletionH0_isModuleComplete R f)

/-- 反復したH⁰は、二つ目の元dについても導来完備。 -/
theorem iteratedCompletion_isModuleComplete_second (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    IsModuleComplete R d (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  let := principalCompletionAlgebra (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)
  let := iteratedCompletionAlgebra R f d
  let _ : IsScalarTower R (PrincipalCompletionH0 R f) (IteratedCompletionH0 R f d) :=
    ⟨fun r s x ↦ by
      change (r • s) • x = (principalCompletionUnitRingHom R f r) • (s • x)
      rw [Algebra.smul_def (R := R) (A := PrincipalCompletionH0 R f)]
      exact mul_smul (principalCompletionUnitRingHom R f r) s x⟩
  exact (isModuleComplete_algebraMap_iff R (PrincipalCompletionH0 R f) d
    (IteratedCompletionH0 R f d)).mp
      (principalCompletionH0_isModuleComplete (PrincipalCompletionH0 R f)
        (principalCompletionUnitRingHom R f d))

/-- 反復した代数構造は、標準環準同型から得られる代数構造と一致する。 -/
theorem iteratedCompletionAlgebra_eq_toAlgebra (f d : R) :
    letI := iteratedCompletionCommRing R f d
    iteratedCompletionAlgebra R f d = (iteratedCompletionUnitRingHom R f d).toAlgebra := by
  let := iteratedCompletionCommRing R f d
  exact Algebra.algebra_ext _ _ (fun r ↦ iteratedCompletion_algebraMap R f d r)

/-- 標準環準同型による作用の下で、fについて導来完備。 -/
theorem iteratedCompletion_isModuleComplete_unit_first (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := (iteratedCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R f (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := iteratedCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (IteratedCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R f (ModuleCat.of R (IteratedCompletionH0 R f d)))
      (iteratedCompletionAlgebra_eq_toAlgebra R f d))
        (iteratedCompletion_isModuleComplete_first R f d)

/-- 標準環準同型による作用の下で、dについて導来完備。 -/
theorem iteratedCompletion_isModuleComplete_unit_second (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := (iteratedCompletionUnitRingHom R f d).toAlgebra
    IsModuleComplete R d (ModuleCat.of R (IteratedCompletionH0 R f d)) := by
  let := iteratedCompletionCommRing R f d
  exact Eq.mp (congrArg (fun a : Algebra R (IteratedCompletionH0 R f d) ↦
    letI := a
    IsModuleComplete R d (ModuleCat.of R (IteratedCompletionH0 R f d)))
      (iteratedCompletionAlgebra_eq_toAlgebra R f d))
        (iteratedCompletion_isModuleComplete_second R f d)

/-- 二座標に導来完備な離散環への任意の写像は、反復したH⁰から一意に延長する。 -/
theorem iteratedCompletion_existsUnique_ringHom (f d : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := iteratedCompletionCommRing R f d
    ∃! h : IteratedCompletionH0 R f d →+* T,
      h.comp (iteratedCompletionUnitRingHom R f d) = g := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  obtain ⟨h₁, hh₁, hu₁⟩ := principalCompletion_existsUnique_ringHom R f T g hf
  have hd' : letI := (h₁.comp (principalCompletionUnitRingHom R f)).toAlgebra
      IsModuleComplete R d (ModuleCat.of R T) := by
    exact Eq.mpr (congrArg (fun q : R →+* T ↦
      letI := q.toAlgebra
      IsModuleComplete R d (ModuleCat.of R T)) hh₁) hd
  have hdS := (isModuleComplete_ringHom_comp_iff R (PrincipalCompletionH0 R f) T
    (principalCompletionUnitRingHom R f) h₁ d).mpr hd'
  obtain ⟨h₂, hh₂, hu₂⟩ := principalCompletion_existsUnique_ringHom
    (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d) T h₁ hdS
  refine ⟨h₂, ?_, ?_⟩
  · change h₂.comp ((principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
      (principalCompletionUnitRingHom R f d)).comp (principalCompletionUnitRingHom R f)) = g
    rw [← RingHom.comp_assoc, hh₂, hh₁]
  · intro k hk
    apply hu₂ k
    apply hu₁
    change (k.comp (principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
      (principalCompletionUnitRingHom R f d))).comp (principalCompletionUnitRingHom R f) = g
    rw [RingHom.comp_assoc]
    exact hk

/-- 二座標に導来完備な離散環への環準同型の、反復したH⁰からの延長
（`iteratedCompletion_existsUnique_ringHom` の写像）。fについて延長してから、dの像について延長する。 -/
def iteratedCompletionLift (f d : R) (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := iteratedCompletionCommRing R f d
    IteratedCompletionH0 R f d →+* T :=
  letI := principalCompletionCommRing R f
  principalCompletionLift (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d) T
    (principalCompletionLift R f T g hf)
    ((isModuleComplete_ringHom_comp_iff R (PrincipalCompletionH0 R f) T
      (principalCompletionUnitRingHom R f) (principalCompletionLift R f T g hf) d).mpr
      (Eq.mpr (congrArg (fun q : R →+* T ↦
        letI := q.toAlgebra
        IsModuleComplete R d (ModuleCat.of R T)) (principalCompletionLift_comp R f T g hf)) hd))

/-- 延長は標準写像との合成で元の環準同型に戻る。 -/
theorem iteratedCompletionLift_comp (f d : R) (T : Type u) [CommRing T] (g : R →+* T)
    (hf : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T))
    (hd : letI := g.toAlgebra; IsModuleComplete R d (ModuleCat.of R T)) :
    letI := iteratedCompletionCommRing R f d
    (iteratedCompletionLift R f d T g hf hd).comp (iteratedCompletionUnitRingHom R f d) = g := by
  letI := principalCompletionCommRing R f
  change (iteratedCompletionLift R f d T g hf hd).comp
    ((principalCompletionUnitRingHom (PrincipalCompletionH0 R f)
      (principalCompletionUnitRingHom R f d)).comp (principalCompletionUnitRingHom R f)) = g
  rw [← RingHom.comp_assoc, iteratedCompletionLift, principalCompletionLift_comp,
    principalCompletionLift_comp]

end SerrePositivity.DerivedCompletion

end IteratedKoszulRingPart

section PairCoordinatesPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R]

/-- 二つの座標を `Fin 2` に並べた列。末尾が二つ目の座標。 -/
def pairKoszulCoordinates (f d : R) : Fin 2 → R := Fin.snoc (fun _ : Fin 1 ↦ f) d

/-- 両座標の完備性を、列の各座標についての条件へ戻す。 -/
theorem pairKoszulCoordinates_isModuleComplete (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) :
    ∀ j, IsModuleComplete R (pairKoszulCoordinates R f d j) N := by
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [pairKoszulCoordinates, Fin.snoc_last] using hd
  · simpa only [pairKoszulCoordinates, Fin.snoc_castSucc] using hf

end SerrePositivity.DerivedCompletion

end PairCoordinatesPart

section ReflectionActionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion.IsCompleteModuleReflection
variable {R : Type u} [CommRing R] {k : ℕ} {a : Fin k → R} {B : ModuleCat.{u} R} {e : B}
    (h : IsCompleteModuleReflection R a B e)
include h

/-- 各座標で完備な加群の元 `n` に、単位候補を `n` へ送る唯一の線形写像を対応させる。 -/
def actionEquiv (N : ModuleCat.{u} R) (hN : ∀ j, IsModuleComplete R (a j) N) :
    N ≃ₗ[R] (B →ₗ[R] N) :=
  (LinearEquiv.ofBijective (LinearMap.applyₗ e) (h.universal N hN)).symm

/-- 対応する線形写像は単位候補を元の元へ送る。 -/
theorem actionEquiv_unit (N : ModuleCat.{u} R) (hN : ∀ j, IsModuleComplete R (a j) N) (n : N) :
    h.actionEquiv N hN n e = n :=
  (LinearEquiv.ofBijective (LinearMap.applyₗ e) (h.universal N hN)).apply_symm_apply n

/-- 線形写像は、単位候補での値に対応する写像そのもの。 -/
theorem actionEquiv_eq (N : ModuleCat.{u} R) (hN : ∀ j, IsModuleComplete R (a j) N)
    (g : B →ₗ[R] N) : h.actionEquiv N hN (g e) = g :=
  (LinearEquiv.ofBijective (LinearMap.applyₗ e) (h.universal N hN)).symm_apply_apply g

/-- 作用は反映の積と両立する。`x` の関数として両辺を単位候補で比べる。 -/
theorem actionEquiv_mul (N : ModuleCat.{u} R) (hN : ∀ j, IsModuleComplete R (a j) N)
    (x y : B) (n : N) :
    h.actionEquiv N hN n (h.mul x y) = h.actionEquiv N hN (h.actionEquiv N hN n y) x := by
  have hg := h.actionEquiv_eq N hN
    ((h.actionEquiv N hN n).comp ((LinearMap.applyₗ y).comp h.leftMultiplication))
  have h1 : ((h.actionEquiv N hN n).comp ((LinearMap.applyₗ y).comp h.leftMultiplication)) e =
      h.actionEquiv N hN n y := by
    change h.actionEquiv N hN n (h.mul e y) = _
    rw [h.unit_mul]
  rw [h1] at hg
  exact (LinearMap.congr_fun hg x).symm

/-- 完備な加群の間の線形写像は作用を保つ。 -/
theorem map_actionEquiv (N₁ : ModuleCat.{u} R) (hN₁ : ∀ j, IsModuleComplete R (a j) N₁)
    (N₂ : ModuleCat.{u} R) (hN₂ : ∀ j, IsModuleComplete R (a j) N₂)
    (g : N₁ →ₗ[R] N₂) (n : N₁) (x : B) :
    g (h.actionEquiv N₁ hN₁ n x) = h.actionEquiv N₂ hN₂ (g n) x := by
  have hg := h.actionEquiv_eq N₂ hN₂ (g.comp (h.actionEquiv N₁ hN₁ n))
  have h1 : (g.comp (h.actionEquiv N₁ hN₁ n)) e = g n := by
    change g (h.actionEquiv N₁ hN₁ n e) = g n
    rw [h.actionEquiv_unit]
  rw [h1] at hg
  exact (LinearMap.congr_fun hg x).symm

/-- 各座標で完備な加群は、反映の環の加群になる。 -/
@[instance_reducible] def completeModule (N : ModuleCat.{u} R)
    (hN : ∀ j, IsModuleComplete R (a j) N) : letI := h.commRing; Module B N := by
  letI := h.commRing
  exact
    { smul := fun x n ↦ h.actionEquiv N hN n x
      one_smul := fun n ↦ h.actionEquiv_unit N hN n
      mul_smul := fun x y n ↦ h.actionEquiv_mul N hN x y n
      smul_zero := fun x ↦ by
        change h.actionEquiv N hN 0 x = 0
        rw [map_zero, LinearMap.zero_apply]
      smul_add := fun x n m ↦ by
        change h.actionEquiv N hN (n + m) x = h.actionEquiv N hN n x + h.actionEquiv N hN m x
        rw [map_add, LinearMap.add_apply]
      add_smul := fun x y n ↦ (h.actionEquiv N hN n).map_add x y
      zero_smul := fun n ↦ (h.actionEquiv N hN n).map_zero }

/-- この作用は元の `R` 作用を延長する。 -/
theorem completeModule_isScalarTower (N : ModuleCat.{u} R)
    (hN : ∀ j, IsModuleComplete R (a j) N) :
    letI := h.commRing; letI := h.algebra; letI := h.completeModule N hN
    IsScalarTower R B N := by
  letI := h.commRing
  letI := h.algebra
  letI := h.completeModule N hN
  exact ⟨fun r x n ↦ by
    change h.actionEquiv N hN n (r • x) = r • h.actionEquiv N hN n x
    rw [map_smul]⟩

end SerrePositivity.DerivedCompletion.IsCompleteModuleReflection

end ReflectionActionPart

section IteratedReflectionPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 反復したH⁰は、両方の座標について完備な加群への反映で、単位候補は1。
一つ目の座標で完備な加群の一つ目の H⁰ の作用（`IsCompleteModuleReflection.completeModule`）を通して、
`R` 線形写像が `S` 線形になることから、二度目の反映の普遍性に帰着する。 -/
theorem iteratedCompletion_isCompleteModuleReflection (f d : R) :
    letI := iteratedCompletionCommRing R f d
    letI := iteratedCompletionAlgebra R f d
    IsCompleteModuleReflection R (pairKoszulCoordinates R f d)
      (ModuleCat.of R (IteratedCompletionH0 R f d)) (1 : IteratedCompletionH0 R f d) := by
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  let := iteratedCompletionCommRing R f d
  let := principalCompletionAlgebra (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)
  let := iteratedCompletionAlgebra R f d
  have hS := principalCompletionH0_isCompleteModuleReflection R f
  have hI := principalCompletionH0_isCompleteModuleReflection (PrincipalCompletionH0 R f)
    (principalCompletionUnitRingHom R f d)
  have tI : IsScalarTower R (PrincipalCompletionH0 R f) (IteratedCompletionH0 R f d) :=
    ⟨fun r s x ↦ by
      change (r • s) • x = (principalCompletionUnitRingHom R f r) • (s • x)
      rw [Algebra.smul_def (R := R) (A := PrincipalCompletionH0 R f)]
      exact mul_smul (principalCompletionUnitRingHom R f r) s x⟩
  refine ⟨pairKoszulCoordinates_isModuleComplete R f d _
    (iteratedCompletion_isModuleComplete_first R f d)
    (iteratedCompletion_isModuleComplete_second R f d), ?_⟩
  intro N hN
  have hNf : ∀ _ : Fin 1, IsModuleComplete R f N := fun _ ↦ by
    simpa only [pairKoszulCoordinates, Fin.snoc_apply_zero] using hN 0
  have hNd : IsModuleComplete R d N := by
    simpa only [pairKoszulCoordinates, Fin.snoc_last] using hN (Fin.last 1)
  letI := hS.completeModule N hNf
  have tN : IsScalarTower R (PrincipalCompletionH0 R f) N := hS.completeModule_isScalarTower N hNf
  have hNS : IsModuleComplete (PrincipalCompletionH0 R f) (principalCompletionUnitRingHom R f d)
      (ModuleCat.of (PrincipalCompletionH0 R f) N) :=
    (isModuleComplete_algebraMap_iff R (PrincipalCompletionH0 R f) d N).mpr hNd
  have hb := hI.universal (ModuleCat.of (PrincipalCompletionH0 R f) N) (fun _ ↦ hNS)
  -- `R` 線形写像は `S` 作用を保つ：`s ↦ g (s • x)` を単位候補で比べる。
  have hlin : ∀ (g : ModuleCat.of R (IteratedCompletionH0 R f d) →ₗ[R] N)
      (s : PrincipalCompletionH0 R f) (x : IteratedCompletionH0 R f d), g (s • x) = s • g x := by
    intro g s x
    let ψ : PrincipalCompletionH0 R f →ₗ[R] N :=
      g.comp ((LinearMap.toSpanSingleton (PrincipalCompletionH0 R f)
        (IteratedCompletionH0 R f d) x).restrictScalars R)
    have hψ := hS.actionEquiv_eq N hNf ψ
    have h1 : ψ (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) 1) = g x := by
      change g ((1 : PrincipalCompletionH0 R f) • x) = g x
      rw [one_smul]
    rw [h1] at hψ
    exact (LinearMap.congr_fun hψ s).symm
  let toS : (ModuleCat.of R (IteratedCompletionH0 R f d) →ₗ[R] N) →
      (IteratedCompletionH0 R f d →ₗ[PrincipalCompletionH0 R f] N) := fun g ↦
    { toFun := g
      map_add' := g.map_add
      map_smul' := hlin g }
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun n ↦ ?_⟩
  · have h12 : toS g₁ = toS g₂ := hb.injective hg
    ext x
    exact LinearMap.congr_fun h12 x
  · obtain ⟨G, hG⟩ := hb.surjective n
    exact ⟨G.restrictScalars R, hG⟩

end SerrePositivity.DerivedCompletion

end IteratedReflectionPart
