module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalReflectionComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionTransport
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.LinearCombination

/-! # 一座標のKoszul塔に現れるサイクルと境界の具体的な表示

次数0のサイクルは δ₁x = (fⁿyₙ) を満たす列の組、境界は ((fⁿzₙ), δ_fz) である。
そのサイクル／境界を列の商表示へ同定する。実際のmapping coneの成分との比較は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 各段でfの冪を掛ける。 -/
def principalPowerMap (f : R) : (ℕ → R) →ₗ[R] (ℕ → R) where
  toFun x n := f ^ n * x n
  map_add' x y := by funext n; exact mul_add _ _ _
  map_smul' r x := by funext n; simp [smul_eq_mul]; ring

/-- 一座標の塔の次数0のサイクル条件。 -/
def principalTowerObstruction (f : R) : ((ℕ → R) × (ℕ → R)) →ₗ[R] (ℕ → R) :=
  (adicRecurrenceMap (1 : R)).comp (LinearMap.fst R _ _) -
    (principalPowerMap R f).comp (LinearMap.snd R _ _)

/-- 具体的な次数0サイクル。 -/
abbrev PrincipalTowerCycles (f : R) := (principalTowerObstruction R f).ker

/-- 次数−1からの具体的な境界。 -/
def principalTowerBoundaryPair (f : R) : (ℕ → R) →ₗ[R] ((ℕ → R) × (ℕ → R)) :=
  (principalPowerMap R f).prod (adicRecurrenceMap f)

/-- この境界はサイクルになる。 -/
theorem principalTowerBoundaryPair_cycle (f : R) (z : ℕ → R) :
    principalTowerObstruction R f (principalTowerBoundaryPair R f z) = 0 := by
  funext n
  simp [principalTowerObstruction, principalTowerBoundaryPair, principalPowerMap,
    adicRecurrenceMap, pow_succ]
  ring

/-- サイクル加群を値にとる境界写像。 -/
def principalTowerBoundary (f : R) : (ℕ → R) →ₗ[R] PrincipalTowerCycles R f :=
  (principalTowerBoundaryPair R f).codRestrict _ (principalTowerBoundaryPair_cycle R f)

/-- サイクルの第一成分は、始値と第二成分から一意に決まる。 -/
theorem principalTowerCycles_ext (f : R) (x y : PrincipalTowerCycles R f)
    (h0 : x.val.1 0 = y.val.1 0) (h2 : x.val.2 = y.val.2) : x = y := by
  apply Subtype.ext
  apply Prod.ext
  · funext n
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hx := congrFun x.property n
      have hy := congrFun y.property n
      dsimp [principalTowerObstruction, principalPowerMap, adicRecurrenceMap] at hx hy
      change (x.val.1 n - 1 * x.val.1 (n + 1)) - f ^ n * x.val.2 n = 0 at hx
      change (y.val.1 n - 1 * y.val.1 (n + 1)) - f ^ n * y.val.2 n = 0 at hy
      simp only [one_mul, ih, h2] at hx hy
      apply sub_eq_zero.mp
      linear_combination -hx + hy
  · exact h2

/-- サイクルの第一成分を始値から再帰的に構成する。 -/
def principalTowerPrefix (f r : R) (y : ℕ → R) : ℕ → R
  | 0 => r
  | n + 1 => principalTowerPrefix f r y n - f ^ n * y n

/-- 任意の始値と第二成分からサイクルを構成できる。 -/
def principalTowerCycleOfCoordinates (f r : R) (y : ℕ → R) : PrincipalTowerCycles R f :=
  ⟨(principalTowerPrefix R f r y, y), by
    funext n
    dsimp [principalTowerObstruction, principalPowerMap, adicRecurrenceMap]
    change (principalTowerPrefix R f r y n - 1 * principalTowerPrefix R f r y (n + 1)) -
      f ^ n * y n = 0
    simp only [one_mul, principalTowerPrefix]
    ring⟩

/-- 始値と第二成分によるサイクルの座標同型。 -/
def principalTowerCycleCoordinates (f : R) :
    PrincipalTowerCycles R f ≃ₗ[R] R × (ℕ → R) where
  toFun x := (x.val.1 0, x.val.2)
  invFun x := principalTowerCycleOfCoordinates R f x.1 x.2
  left_inv x := principalTowerCycles_ext R f _ x rfl rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- サイクルを「始値の一項列−第二成分」の類へ送る。 -/
def principalTowerCycleClass (f : R) :
    PrincipalTowerCycles R f →ₗ[R] PrincipalReflectionModule R f :=
  (principalReflectionMk R f).comp
    (((sequenceHead R).comp (LinearMap.fst R _ _) - LinearMap.snd R _ _).comp
      (principalTowerCycleCoordinates R f).toLinearMap)

/-- 境界の第二成分の漸化式と、列の商の関係式との符号。 -/
theorem principalReflectionRelation_tail (f : R) (z : ℕ → R) :
    sequenceHead R (z 0) - adicRecurrenceMap f z =
      -principalReflectionRelation R f (sequenceTail R z) := by
  funext n
  cases n <;> simp [sequenceHead, sequenceTail, adicRecurrenceMap,
    principalReflectionRelation]

/-- 境界は列の商で零になる。 -/
theorem principalTowerCycleClass_boundary (f : R) (z : ℕ → R) :
    principalTowerCycleClass R f (principalTowerBoundary R f z) = 0 := by
  change principalReflectionMk R f
    (sequenceHead R (f ^ 0 * z 0) - adicRecurrenceMap f z) = 0
  rw [pow_zero, one_mul, principalReflectionRelation_tail, map_neg]
  rw [show principalReflectionMk R f (principalReflectionRelation R f (sequenceTail R z)) = 0
    from (Submodule.Quotient.mk_eq_zero _).mpr ⟨sequenceTail R z, rfl⟩, neg_zero]

/-- サイクルから列の商への写像は全射。 -/
theorem principalTowerCycleClass_surjective (f : R) :
    Function.Surjective (principalTowerCycleClass R f) := by
  intro t
  obtain ⟨z, rfl⟩ := (principalReflectionRelation R f).range.mkQ_surjective t
  refine ⟨principalTowerCycleOfCoordinates R f 0 (-z), ?_⟩
  change principalReflectionMk R f (sequenceHead R 0 - -z) = principalReflectionMk R f z
  rw [map_zero, sub_neg_eq_add, zero_add]

/-- 列の商で零になるサイクルは境界。 -/
theorem principalTowerCycleClass_eq_zero_iff (f : R) (x : PrincipalTowerCycles R f) :
    principalTowerCycleClass R f x = 0 ↔ ∃ z, principalTowerBoundary R f z = x := by
  constructor
  · intro hx
    have hm : sequenceHead R (x.val.1 0) - x.val.2 ∈
        (principalReflectionRelation R f).range :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨w, hw⟩ := hm
    let z := sequenceHead R (x.val.1 0) - sequenceShiftRight R w
    have hz0 : z 0 = x.val.1 0 := by simp [z, sequenceHead]
    have hzt : sequenceTail R z = -w := by
      funext n
      simp [z, sequenceTail, sequenceHead]
    have hzy : adicRecurrenceMap f z = x.val.2 := by
      have he := principalReflectionRelation_tail R f z
      rw [hz0, hzt, map_neg, neg_neg, hw] at he
      exact (sub_right_inj).mp he
    refine ⟨z, principalTowerCycles_ext R f _ x ?_ ?_⟩
    · change f ^ 0 * z 0 = x.val.1 0
      simpa using hz0
    · exact hzy
  · rintro ⟨z, rfl⟩
    exact principalTowerCycleClass_boundary R f z

/-- 境界の像が、サイクルから列の商への写像の核に一致する。 -/
theorem principalTowerBoundary_range (f : R) :
    (principalTowerBoundary R f).range = (principalTowerCycleClass R f).ker := by
  ext x
  exact (principalTowerCycleClass_eq_zero_iff R f x).symm

/-- 具体的なサイクル／境界と、主元完備化の列の商との線形同型。 -/
def principalTowerCycleQuotientEquiv (f : R) :
    (PrincipalTowerCycles R f ⧸ (principalTowerBoundary R f).range) ≃ₗ[R]
      PrincipalReflectionModule R f :=
  (Submodule.quotEquivOfEq _ _ (principalTowerBoundary_range R f)).trans
    (LinearMap.quotKerEquivOfSurjective _ (principalTowerCycleClass_surjective R f))

/-- この同型は、定数サイクルから来る単位を保つ。 -/
theorem principalTowerCycleQuotientEquiv_unit (f : R) :
    principalTowerCycleQuotientEquiv R f
      (Submodule.Quotient.mk (principalTowerCycleOfCoordinates R f 1 0)) =
      principalReflectionUnit R f := by
  change principalReflectionMk R f (sequenceHead R 1 - 0) = _
  rw [sub_zero]
  rfl

/-- 具体的な三項モデルの短複体。 -/
def principalTowerShortComplex (f : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (principalTowerBoundaryPair R f) (principalTowerObstruction R f)
    (by apply LinearMap.ext; intro z; exact principalTowerBoundaryPair_cycle R f z)

/-- 三項モデルの実際のホモロジーから、列の商表示への同型。 -/
def principalTowerHomologyEquiv (f : R) :
    (principalTowerShortComplex R f).homology ≃ₗ[R] PrincipalReflectionModule R f :=
  (principalTowerShortComplex R f).moduleCatHomologyIso.toLinearEquiv.trans
    (principalTowerCycleQuotientEquiv R f)

/-- 定数列に対応するサイクル。 -/
def principalTowerConstantCycle (f : R) : R →ₗ[R] PrincipalTowerCycles R f :=
  (principalTowerCycleCoordinates R f).symm.toLinearMap.comp (LinearMap.inl R R (ℕ → R))

/-- 第二成分が零なら第一成分は定数列になる。 -/
theorem principalTowerPrefix_zero (f r : R) (n : ℕ) :
    principalTowerPrefix R f r 0 n = r := by
  induction n with
  | zero => rfl
  | succ n ih => simp [principalTowerPrefix, ih]

/-- 標準サイクルは実際に定数列と零列の組である。 -/
theorem principalTowerConstantCycle_val (f r : R) :
    (principalTowerConstantCycle R f r).val = (fun _ ↦ r, 0) := by
  apply Prod.ext
  · funext n
    exact principalTowerPrefix_zero R f r n
  · rfl

/-- 定数サイクルからホモロジーへの標準写像。 -/
def principalTowerHomologyUnit (f : R) : R →ₗ[R] (principalTowerShortComplex R f).homology :=
  (principalTowerShortComplex R f).homologyπ.hom.comp
    ((principalTowerShortComplex R f).moduleCatCyclesIso.inv.hom.comp
      (principalTowerConstantCycle R f))

/-- ホモロジーの同型は、標準写像を最初の一項列の類へ送る。 -/
theorem principalTowerHomologyEquiv_unit (f r : R) :
    principalTowerHomologyEquiv R f (principalTowerHomologyUnit R f r) =
      principalReflectionMk R f (sequenceHead R r) := by
  let S := principalTowerShortComplex R f
  let c := principalTowerConstantCycle R f r
  have he := congrArg (fun g ↦ g.hom c) S.moduleCatCyclesIso_inv_π
  change S.homologyπ (S.moduleCatCyclesIso.inv c) =
    S.moduleCatHomologyIso.inv (Submodule.Quotient.mk c) at he
  change principalTowerCycleQuotientEquiv R f
    (S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv c))) = _
  rw [he]
  have hi := congrArg (fun g ↦ g.hom (Submodule.Quotient.mk c)) S.moduleCatHomologyIso.inv_hom_id
  change S.moduleCatHomologyIso.hom (S.moduleCatHomologyIso.inv (Submodule.Quotient.mk c)) =
    Submodule.Quotient.mk c at hi
  rw [hi]
  change principalReflectionMk R f (sequenceHead R r - 0) = _
  rw [sub_zero]

/-- 具体的な三項モデルのホモロジーは、標準元について完備加群への反映になる。 -/
theorem principalTowerHomology_isCompleteModuleReflection (f : R) :
    IsCompleteModuleReflection R (fun _ : Fin 1 ↦ f)
      (principalTowerShortComplex R f).homology (principalTowerHomologyUnit R f 1) :=
  (principalReflection_isCompleteModuleReflection R f).of_linearEquiv R
    (principalTowerHomologyEquiv R f).symm (by
      apply (principalTowerHomologyEquiv R f).injective
      rw [LinearEquiv.apply_symm_apply, principalTowerHomologyEquiv_unit]
      rfl)

end SerrePositivity.DerivedCompletion
