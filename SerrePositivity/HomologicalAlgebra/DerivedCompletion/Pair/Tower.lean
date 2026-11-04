module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation

/-! # 二つの座標の Koszul 塔の H⁰ の三項模型

## 概要

二つの座標の Koszul 塔の H⁰ のサイクル（`δ₁x = dⁿaₙ + fⁿbₙ`）と交差項を含む境界を三項の行列で表し（`PairTowerCycles`）、始値と二つの列の和から完備加群への評価を作って全境界の消滅を示す。一つの座標のサイクルを二通りに埋め込み、二つの座標のサイクルをその和へ分解して延長の一意性を示す。

## 方針

列の和は `ModuleComplete/Presentation` の `completeSequenceSum` を使う。

## 規約

実際の Koszul 塔の成分との比較は `Pair/Koszul`。旧 `PairTowerPresentation`・`PairTowerEvaluation`・`PairTowerUniqueness`（2b の B で一つの座標の反復に置き換える候補）。

## 使われ方

`Pair/Koszul`。
-/

@[expose] public noncomputable section

universe u

section PairTowerPresentationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 二座標の次数0サイクルの障害写像。 -/
def pairTowerObstruction (f d : R) :
    ((ℕ → R) × ((ℕ → R) × (ℕ → R))) →ₗ[R] (ℕ → R) :=
  (adicRecurrenceMap (1 : R)).comp (LinearMap.fst R _ _) -
    (principalPowerMap R d).comp ((LinearMap.fst R _ _).comp (LinearMap.snd R _ _)) -
      (principalPowerMap R f).comp ((LinearMap.snd R _ _).comp (LinearMap.snd R _ _))

/-- 二座標の次数0サイクル。 -/
abbrev PairTowerCycles (f d : R) := (pairTowerObstruction R f d).ker

/-- 二座標の次数−1からの境界。第三変数が交差境界を表す。 -/
def pairTowerBoundaryTriple (f d : R) :
    (((ℕ → R) × (ℕ → R)) × (ℕ → R)) →ₗ[R]
      ((ℕ → R) × ((ℕ → R) × (ℕ → R))) :=
  ((principalPowerMap R d).comp ((LinearMap.fst R _ _).comp (LinearMap.fst R _ _)) +
    (principalPowerMap R f).comp ((LinearMap.snd R _ _).comp (LinearMap.fst R _ _))).prod
      (((adicRecurrenceMap d).comp ((LinearMap.fst R _ _).comp (LinearMap.fst R _ _)) -
        (principalPowerMap R f).comp (LinearMap.snd R _ _)).prod
          ((adicRecurrenceMap f).comp ((LinearMap.snd R _ _).comp (LinearMap.fst R _ _)) +
            (principalPowerMap R d).comp (LinearMap.snd R _ _)))

/-- 交差項を含む境界はサイクルになる。 -/
theorem pairTowerBoundaryTriple_cycle (f d : R)
    (z : ((ℕ → R) × (ℕ → R)) × (ℕ → R)) :
    pairTowerObstruction R f d (pairTowerBoundaryTriple R f d z) = 0 := by
  funext n
  simp [pairTowerObstruction, pairTowerBoundaryTriple, principalPowerMap, adicRecurrenceMap,
    pow_succ]
  ring

/-- サイクル加群を値にとる二座標の境界写像。 -/
def pairTowerBoundary (f d : R) :
    (((ℕ → R) × (ℕ → R)) × (ℕ → R)) →ₗ[R] PairTowerCycles R f d :=
  (pairTowerBoundaryTriple R f d).codRestrict _ (pairTowerBoundaryTriple_cycle R f d)

/-- 第一列は始値と二つの補助列から一意に決まる。 -/
theorem pairTowerCycles_ext (f d : R) (x y : PairTowerCycles R f d)
    (h0 : x.val.1 0 = y.val.1 0) (h2 : x.val.2 = y.val.2) : x = y := by
  apply Subtype.ext
  apply Prod.ext
  · funext n
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hx := congrFun x.property n
      have hy := congrFun y.property n
      dsimp [pairTowerObstruction, principalPowerMap, adicRecurrenceMap] at hx hy
      change (x.val.1 n - 1 * x.val.1 (n + 1)) - d ^ n * x.val.2.1 n -
        f ^ n * x.val.2.2 n = 0 at hx
      change (y.val.1 n - 1 * y.val.1 (n + 1)) - d ^ n * y.val.2.1 n -
        f ^ n * y.val.2.2 n = 0 at hy
      simp only [one_mul, ih, h2] at hx hy
      apply sub_eq_zero.mp
      linear_combination -hx + hy
  · exact h2

/-- 二つの補助列と始値から第一列を構成する。 -/
def pairTowerPrefix (f d r : R) (a b : ℕ → R) : ℕ → R
  | 0 => r
  | n + 1 => pairTowerPrefix f d r a b n - d ^ n * a n - f ^ n * b n

/-- 任意の始値と補助列による二座標のサイクル。 -/
def pairTowerCycleOfCoordinates (f d r : R) (a b : ℕ → R) : PairTowerCycles R f d :=
  ⟨(pairTowerPrefix R f d r a b, (a, b)), by
    funext n
    dsimp [pairTowerObstruction, principalPowerMap, adicRecurrenceMap]
    change (pairTowerPrefix R f d r a b n - 1 * pairTowerPrefix R f d r a b (n + 1)) -
      d ^ n * a n - f ^ n * b n = 0
    simp only [one_mul, pairTowerPrefix]
    ring⟩

/-- 始値と二つの補助列によるサイクルの座標同型。 -/
def pairTowerCycleCoordinates (f d : R) :
    PairTowerCycles R f d ≃ₗ[R] R × ((ℕ → R) × (ℕ → R)) where
  toFun x := (x.val.1 0, x.val.2)
  invFun x := pairTowerCycleOfCoordinates R f d x.1 x.2.1 x.2.2
  left_inv x := pairTowerCycles_ext R f d _ x rfl rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 交差境界を保持した実際の三項短複体。 -/
def pairTowerShortComplex (f d : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (pairTowerBoundaryTriple R f d) (pairTowerObstruction R f d)
    (by apply LinearMap.ext; intro z; exact pairTowerBoundaryTriple_cycle R f d z)

/-- 二座標の定数サイクルへの標準写像。 -/
def pairTowerConstantCycle (f d : R) : R →ₗ[R] PairTowerCycles R f d :=
  (pairTowerCycleCoordinates R f d).symm.toLinearMap.comp
    (LinearMap.inl R R ((ℕ → R) × (ℕ → R)))

/-- 補助列が零なら第一列は定数列。 -/
theorem pairTowerPrefix_zero (f d r : R) (n : ℕ) :
    pairTowerPrefix R f d r 0 0 n = r := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairTowerPrefix, ih]

/-- 標準サイクルの具体的な列。 -/
theorem pairTowerConstantCycle_val (f d r : R) :
    (pairTowerConstantCycle R f d r).val = (fun _ ↦ r, (0, 0)) := by
  apply Prod.ext
  · funext n
    exact pairTowerPrefix_zero R f d r n
  · rfl

/-- 三項モデルのH⁰への標準写像。 -/
def pairTowerHomologyUnit (f d : R) : R →ₗ[R] (pairTowerShortComplex R f d).homology :=
  (pairTowerShortComplex R f d).homologyπ.hom.comp
    ((pairTowerShortComplex R f d).moduleCatCyclesIso.inv.hom.comp
      (pairTowerConstantCycle R f d))

end SerrePositivity.DerivedCompletion

end PairTowerPresentationPart

section PairTowerEvaluationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- サイクルの始値から二つの列の和を引く線形評価。 -/
def pairTowerCycleEvaluation (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    PairTowerCycles R f d →ₗ[R] N :=
  (((LinearMap.toSpanSingleton R N t).comp (LinearMap.fst R _ _) -
    (completeSequenceSum R d N hd).comp ((sequenceScalarMap R N t).comp
      ((LinearMap.fst R _ _).comp (LinearMap.snd R _ _)))) -
    (completeSequenceSum R f N hf).comp ((sequenceScalarMap R N t).comp
      ((LinearMap.snd R _ _).comp (LinearMap.snd R _ _)))).comp
        (pairTowerCycleCoordinates R f d).toLinearMap

@[simp] theorem pairTowerCycleEvaluation_apply (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N)
    (c : PairTowerCycles R f d) :
    pairTowerCycleEvaluation R f d N hf hd t c = c.val.1 0 • t -
      completeSequenceSum R d N hd (sequenceScalarMap R N t c.val.2.1) -
        completeSequenceSum R f N hf (sequenceScalarMap R N t c.val.2.2) := rfl

/-- 係数の漸化式を、指定した元のスカラー倍の漸化式へ移す。 -/
theorem sequenceScalarMap_recurrence (a : R) (N : ModuleCat.{u} R) (t : N)
    (x : ℕ → R) :
    sequenceScalarMap R N t (adicRecurrenceMap a x) =
      adicRecurrenceMap a (sequenceScalarMap R N t x) := by
  funext n
  simp [sequenceScalarMap, adicRecurrenceMap, sub_smul, mul_smul]

/-- 係数の冪による重みを、加群上のスカラー作用へ移す。 -/
theorem sequenceScalarMap_power (a : R) (N : ModuleCat.{u} R) (t : N)
    (x : ℕ → R) :
    sequenceScalarMap R N t (principalPowerMap R a x) =
      fun n ↦ a ^ n • (sequenceScalarMap R N t x n) := by
  funext n
  simp [sequenceScalarMap, principalPowerMap, mul_smul]

/-- 二つの通常の境界と交差境界のすべてが、完備加群への評価で消える。 -/
theorem pairTowerCycleEvaluation_boundary (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N)
    (z : ((ℕ → R) × (ℕ → R)) × (ℕ → R)) :
    pairTowerCycleEvaluation R f d N hf hd t (pairTowerBoundary R f d z) = 0 := by
  rw [pairTowerCycleEvaluation_apply]
  change (d ^ 0 * z.1.1 0 + f ^ 0 * z.1.2 0) • t -
    completeSequenceSum R d N hd (sequenceScalarMap R N t
      (adicRecurrenceMap d z.1.1 - principalPowerMap R f z.2)) -
    completeSequenceSum R f N hf (sequenceScalarMap R N t
      (adicRecurrenceMap f z.1.2 + principalPowerMap R d z.2)) = 0
  rw [map_sub, map_add, map_sub, map_add, sequenceScalarMap_recurrence,
    sequenceScalarMap_recurrence, completeSequenceSum_recurrence, completeSequenceSum_recurrence,
    sequenceScalarMap_power, sequenceScalarMap_power, completeSequenceSum_cross R f d N hf hd]
  simp [sequenceScalarMap, add_smul]

/-- 境界を消す評価を、サイクルの商へ降ろす。 -/
def pairTowerQuotientEvaluation (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) →ₗ[R] N :=
  (pairTowerBoundary R f d).range.liftQ (pairTowerCycleEvaluation R f d N hf hd t) (by
    rintro c ⟨z, rfl⟩
    exact pairTowerCycleEvaluation_boundary R f d N hf hd t z)

/-- 定数サイクルは、指定したスカラー倍へ送られる。 -/
theorem pairTowerQuotientEvaluation_unit (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) (r : R) :
    pairTowerQuotientEvaluation R f d N hf hd t
      (Submodule.Quotient.mk (pairTowerConstantCycle R f d r)) = r • t := by
  change pairTowerCycleEvaluation R f d N hf hd t (pairTowerConstantCycle R f d r) = _
  rw [pairTowerCycleEvaluation_apply, pairTowerConstantCycle_val]
  simp

/-- 標準ホモロジーを、具体的なサイクルの商へ同定する。 -/
def pairTowerHomologyQuotientEquiv (f d : R) :
    (pairTowerShortComplex R f d).homology ≃ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (pairTowerShortComplex R f d).moduleCatHomologyIso.toLinearEquiv

/-- サイクルの商との同定は、標準写像を保つ。 -/
theorem pairTowerHomologyQuotientEquiv_unit (f d r : R) :
    pairTowerHomologyQuotientEquiv R f d (pairTowerHomologyUnit R f d r) =
      Submodule.Quotient.mk (pairTowerConstantCycle R f d r) := by
  let S := pairTowerShortComplex R f d
  let c := pairTowerConstantCycle R f d r
  have h := congrArg (fun g ↦ g.hom (S.moduleCatCyclesIso.inv c))
    S.π_moduleCatCyclesIso_hom
  change S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv c)) =
    Submodule.Quotient.mk (S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv c)) at h
  have hi := congrArg (fun g ↦ g.hom c) S.moduleCatCyclesIso.inv_hom_id
  change S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv c) = c at hi
  rw [hi] at h
  exact h

/-- 三項モデルの実際のホモロジーから、完備加群への線形評価。 -/
def pairTowerHomologyEvaluation (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    (pairTowerShortComplex R f d).homology →ₗ[R] N :=
  (pairTowerQuotientEvaluation R f d N hf hd t).comp
    (pairTowerShortComplex R f d).moduleCatHomologyIso.hom.hom

/-- ホモロジーの評価も、標準写像を指定したスカラー倍へ送る。 -/
theorem pairTowerHomologyEvaluation_unit (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) (r : R) :
    pairTowerHomologyEvaluation R f d N hf hd t (pairTowerHomologyUnit R f d r) =
      r • t := by
  change pairTowerQuotientEvaluation R f d N hf hd t
    (pairTowerHomologyQuotientEquiv R f d (pairTowerHomologyUnit R f d r)) = _
  rw [pairTowerHomologyQuotientEquiv_unit]
  exact pairTowerQuotientEvaluation_unit R f d N hf hd t r

/-- 任意の標準元の像を持つ、三項モデルのH⁰からの延長が存在する。 -/
theorem pairTowerHomologyEvaluation_exists (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    ∃ g : (pairTowerShortComplex R f d).homology →ₗ[R] N,
      g (pairTowerHomologyUnit R f d 1) = t := by
  refine ⟨pairTowerHomologyEvaluation R f d N hf hd t, ?_⟩
  rw [pairTowerHomologyEvaluation_unit, one_smul]

end SerrePositivity.DerivedCompletion

end PairTowerEvaluationPart

section PairTowerUniquenessPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- dの一座標サイクルを二座標モデルへ含める。 -/
def pairTowerCyclesFromD (f d : R) : PrincipalTowerCycles R d →ₗ[R] PairTowerCycles R f d where
  toFun c := ⟨(c.val.1, (c.val.2, 0)), by
    change adicRecurrenceMap (1 : R) c.val.1 - principalPowerMap R d c.val.2 -
      principalPowerMap R f 0 = 0
    rw [map_zero, sub_zero]
    exact c.property⟩
  map_add' x y := by apply Subtype.ext; ext <;> simp
  map_smul' r x := by apply Subtype.ext; ext <;> simp

/-- fの一座標サイクルを二座標モデルへ含める。 -/
def pairTowerCyclesFromF (f d : R) : PrincipalTowerCycles R f →ₗ[R] PairTowerCycles R f d where
  toFun c := ⟨(c.val.1, (0, c.val.2)), by
    change adicRecurrenceMap (1 : R) c.val.1 - principalPowerMap R d 0 -
      principalPowerMap R f c.val.2 = 0
    rw [map_zero, sub_zero]
    exact c.property⟩
  map_add' x y := by apply Subtype.ext; ext <;> simp
  map_smul' r x := by apply Subtype.ext; ext <;> simp

/-- dの境界は二座標の通常の境界へ送られる。 -/
theorem pairTowerCyclesFromD_boundary (f d : R) (z : ℕ → R) :
    pairTowerCyclesFromD R f d (principalTowerBoundary R d z) =
      pairTowerBoundary R f d ((z, 0), 0) := by
  apply Subtype.ext
  simp [pairTowerCyclesFromD, principalTowerBoundary, principalTowerBoundaryPair,
    pairTowerBoundary, pairTowerBoundaryTriple]

/-- fの境界は二座標の通常の境界へ送られる。 -/
theorem pairTowerCyclesFromF_boundary (f d : R) (z : ℕ → R) :
    pairTowerCyclesFromF R f d (principalTowerBoundary R f z) =
      pairTowerBoundary R f d ((0, z), 0) := by
  apply Subtype.ext
  simp [pairTowerCyclesFromF, principalTowerBoundary, principalTowerBoundaryPair,
    pairTowerBoundary, pairTowerBoundaryTriple]

/-- 任意の二座標サイクルは、一座標サイクルの二つの像の和。 -/
theorem pairTowerCycles_decomposition (f d : R) (c : PairTowerCycles R f d) :
    c = pairTowerCyclesFromD R f d
      (principalTowerCycleOfCoordinates R d (c.val.1 0) c.val.2.1) +
    pairTowerCyclesFromF R f d (principalTowerCycleOfCoordinates R f 0 c.val.2.2) := by
  apply pairTowerCycles_ext R f d
  · simp [pairTowerCyclesFromD, pairTowerCyclesFromF, principalTowerCycleOfCoordinates,
      principalTowerPrefix]
  · simp [pairTowerCyclesFromD, pairTowerCyclesFromF, principalTowerCycleOfCoordinates]

/-- dの一座標のサイクルの商から二座標のサイクルの商への写像。 -/
def pairTowerQuotientFromD (f d : R) :
    (PrincipalTowerCycles R d ⧸ (principalTowerBoundary R d).range) →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (principalTowerBoundary R d).range.mapQ (pairTowerBoundary R f d).range
    (pairTowerCyclesFromD R f d) (by
      rintro c ⟨z, rfl⟩
      exact ⟨((z, 0), 0), (pairTowerCyclesFromD_boundary R f d z).symm⟩)

/-- fの一座標のサイクルの商から二座標のサイクルの商への写像。 -/
def pairTowerQuotientFromF (f d : R) :
    (PrincipalTowerCycles R f ⧸ (principalTowerBoundary R f).range) →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (principalTowerBoundary R f).range.mapQ (pairTowerBoundary R f d).range
    (pairTowerCyclesFromF R f d) (by
      rintro c ⟨z, rfl⟩
      exact ⟨((0, z), 0), (pairTowerCyclesFromF_boundary R f d z).symm⟩)

/-- dの主元反射加群から二座標の商への標準写像。 -/
def pairTowerReflectionFromD (f d : R) :
    PrincipalReflectionModule R d →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (pairTowerQuotientFromD R f d).comp (principalTowerCycleQuotientEquiv R d).symm.toLinearMap

/-- fの主元反射加群から二座標の商への標準写像。 -/
def pairTowerReflectionFromF (f d : R) :
    PrincipalReflectionModule R f →ₗ[R]
      (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) :=
  (pairTowerQuotientFromF R f d).comp (principalTowerCycleQuotientEquiv R f).symm.toLinearMap

/-- dの反射からの写像は標準元を保つ。 -/
theorem pairTowerReflectionFromD_unit (f d : R) :
    pairTowerReflectionFromD R f d (principalReflectionUnit R d) =
      Submodule.Quotient.mk (pairTowerConstantCycle R f d 1) := by
  rw [← principalTowerCycleQuotientEquiv_unit R d]
  change pairTowerQuotientFromD R f d
    ((principalTowerCycleQuotientEquiv R d).symm ((principalTowerCycleQuotientEquiv R d) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  change Submodule.Quotient.mk (pairTowerCyclesFromD R f d
    (principalTowerCycleOfCoordinates R d 1 0)) = _
  congr 1
  apply pairTowerCycles_ext R f d
  · rfl
  · rfl

/-- fの反射からの写像は標準元を保つ。 -/
theorem pairTowerReflectionFromF_unit (f d : R) :
    pairTowerReflectionFromF R f d (principalReflectionUnit R f) =
      Submodule.Quotient.mk (pairTowerConstantCycle R f d 1) := by
  rw [← principalTowerCycleQuotientEquiv_unit R f]
  change pairTowerQuotientFromF R f d
    ((principalTowerCycleQuotientEquiv R f).symm ((principalTowerCycleQuotientEquiv R f) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  change Submodule.Quotient.mk (pairTowerCyclesFromF R f d
    (principalTowerCycleOfCoordinates R f 1 0)) = _
  congr 1
  apply pairTowerCycles_ext R f d
  · rfl
  · rfl

/-- 標準元を零へ送る完備加群への写像は零。 -/
theorem pairTowerQuotientHom_eq_zero (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N)
    (g : (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) →ₗ[R] N)
    (hg : g (Submodule.Quotient.mk (pairTowerConstantCycle R f d 1)) = 0) : g = 0 := by
  have hD : g.comp (pairTowerReflectionFromD R f d) = 0 :=
    principalReflectionHom_eq_zero R d N hd _ (by
      change g (pairTowerReflectionFromD R f d (principalReflectionUnit R d)) = 0
      rw [pairTowerReflectionFromD_unit, hg])
  have hF : g.comp (pairTowerReflectionFromF R f d) = 0 :=
    principalReflectionHom_eq_zero R f N hf _ (by
      change g (pairTowerReflectionFromF R f d (principalReflectionUnit R f)) = 0
      rw [pairTowerReflectionFromF_unit, hg])
  have hzD (c : PrincipalTowerCycles R d) :
      g (Submodule.Quotient.mk (pairTowerCyclesFromD R f d c)) = 0 := by
    have h := LinearMap.congr_fun hD
      (principalTowerCycleQuotientEquiv R d (Submodule.Quotient.mk c))
    simpa [pairTowerReflectionFromD, pairTowerQuotientFromD] using h
  have hzF (c : PrincipalTowerCycles R f) :
      g (Submodule.Quotient.mk (pairTowerCyclesFromF R f d c)) = 0 := by
    have h := LinearMap.congr_fun hF
      (principalTowerCycleQuotientEquiv R f (Submodule.Quotient.mk c))
    simpa [pairTowerReflectionFromF, pairTowerQuotientFromF] using h
  apply LinearMap.ext
  intro q
  obtain ⟨c, rfl⟩ := (pairTowerBoundary R f d).range.mkQ_surjective q
  rw [pairTowerCycles_decomposition R f d c]
  change g ((pairTowerBoundary R f d).range.mkQ (_ + _)) = 0
  simp only [map_add, Submodule.mkQ_apply, hzD, hzF, add_zero]

/-- ホモロジー上でも、標準元を零へ送る完備加群への写像は零。 -/
theorem pairTowerHomologyHom_eq_zero (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N)
    (g : (pairTowerShortComplex R f d).homology →ₗ[R] N)
    (hg : g (pairTowerHomologyUnit R f d 1) = 0) : g = 0 := by
  let e := pairTowerHomologyQuotientEquiv R f d
  have hu : e.symm (Submodule.Quotient.mk (pairTowerConstantCycle R f d 1)) =
      pairTowerHomologyUnit R f d 1 := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (pairTowerHomologyQuotientEquiv_unit R f d 1).symm
  have hQ : g.comp e.symm.toLinearMap = 0 :=
    pairTowerQuotientHom_eq_zero R f d N hf hd _ (by
      change g (e.symm (Submodule.Quotient.mk (pairTowerConstantCycle R f d 1))) = 0
      rw [hu, hg])
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun hQ (e x)
  simpa using h

/-- 二座標モデルのH⁰からの線形延長は、標準元の像で一意に決まる。 -/
theorem pairTowerHomology_evaluation_bijective (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) :
    Function.Bijective (fun g : (pairTowerShortComplex R f d).homology →ₗ[R] N ↦
      g (pairTowerHomologyUnit R f d 1)) := by
  constructor
  · intro g h he
    apply sub_eq_zero.mp
    exact pairTowerHomologyHom_eq_zero R f d N hf hd (g - h) (sub_eq_zero.mpr he)
  · intro t
    exact pairTowerHomologyEvaluation_exists R f d N hf hd t

end SerrePositivity.DerivedCompletion

end PairTowerUniquenessPart
