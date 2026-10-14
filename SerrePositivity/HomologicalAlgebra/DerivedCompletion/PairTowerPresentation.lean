module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalTowerPresentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteSequenceSum

/-! # 二座標Koszul塔のH⁰に現れる三項行列モデル

サイクル条件は δ₁x = dⁿaₙ + fⁿbₙ。
境界は (dⁿAₙ+fⁿBₙ, δ_d A−fⁿzₙ, δ_f B+dⁿzₙ) で、交差項も保持する。
実際のKoszul塔の成分との比較は別途行う。
-/

@[expose] public noncomputable section
universe u
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
