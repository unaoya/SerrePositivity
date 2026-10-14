module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleHomComplete

/-! # 一つの座標の完備化の、列による加群表示

列の右シフト−f倍の像を商にし、f導来完備加群への写像を漸化式の一意解から構成する。
Koszul完備化のH⁰との同定は別途証明する必要がある。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 列を一つ右へずらし、最初に零を入れる。 -/
def sequenceShiftRight : (ℕ → R) →ₗ[R] (ℕ → R) where
  toFun x n := Nat.casesOn n 0 x
  map_add' x y := by funext n; cases n <;> simp
  map_smul' r x := by funext n; cases n <;> simp

@[simp] theorem sequenceShiftRight_zero (x : ℕ → R) : sequenceShiftRight R x 0 = 0 := rfl
@[simp] theorem sequenceShiftRight_succ (x : ℕ → R) (n : ℕ) :
    sequenceShiftRight R x (n + 1) = x n := rfl

/-- 最初の項を除いた列。 -/
def sequenceTail : (ℕ → R) →ₗ[R] (ℕ → R) where
  toFun x n := x (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 最初の項だけを指定した列。 -/
def sequenceHead : R →ₗ[R] (ℕ → R) where
  toFun r n := Nat.casesOn n r (fun _ ↦ 0)
  map_add' r s := by funext n; cases n <;> simp
  map_smul' r s := by funext n; cases n <;> simp

/-- 列による主元完備化の関係写像。 -/
def principalReflectionRelation (f : R) : (ℕ → R) →ₗ[R] (ℕ → R) :=
  sequenceShiftRight R - f • LinearMap.id

/-- 主元完備化の加群の候補表示。まだKoszulのH⁰とは同一視しない。 -/
abbrev PrincipalReflectionModule (f : R) :=
  (ℕ → R) ⧸ (principalReflectionRelation R f).range

/-- 候補表示への商写像。 -/
def principalReflectionMk (f : R) : (ℕ → R) →ₗ[R] PrincipalReflectionModule R f :=
  (principalReflectionRelation R f).range.mkQ

/-- 1に対応する標準元。 -/
def principalReflectionUnit (f : R) : PrincipalReflectionModule R f :=
  principalReflectionMk R f (sequenceHead R 1)

/-- 商では、右シフトがf倍に等しくなる。 -/
theorem principalReflectionMk_shift (f : R) (x : ℕ → R) :
    principalReflectionMk R f (sequenceShiftRight R x) =
      f • principalReflectionMk R f x := by
  apply sub_eq_zero.mp
  rw [← map_smul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- 商の各列は、最初の係数とf倍した残りの列に分かれる。 -/
theorem principalReflectionMk_decomposition (f : R) (x : ℕ → R) :
    principalReflectionMk R f x =
      x 0 • principalReflectionUnit R f + f • principalReflectionMk R f (sequenceTail R x) := by
  have hx : x = x 0 • sequenceHead R 1 + sequenceShiftRight R (sequenceTail R x) := by
    funext n
    cases n <;> simp [sequenceHead, sequenceTail, smul_eq_mul]
  conv_lhs => rw [hx]
  rw [map_add, map_smul, principalReflectionMk_shift]
  rfl

/-- 完備性判定の列作用を線形同型として使う。 -/
def adicRecurrenceEquiv (f : R) (N : ModuleCat.{u} R) (hN : IsModuleComplete R f N) :
    (ℕ → N) ≃ₗ[R] (ℕ → N) :=
  LinearEquiv.ofBijective (adicRecurrenceMap f)
    ((isModuleComplete_iff_recurrence_bijective R f N).mp hN)

/-- 列の係数を、指定した元のスカラー倍の列へ送る。 -/
def sequenceScalarMap (N : ModuleCat.{u} R) (t : N) : (ℕ → R) →ₗ[R] (ℕ → N) where
  toFun x n := x n • t
  map_add' x y := by funext n; exact add_smul _ _ _
  map_smul' r x := by funext n; exact mul_smul _ _ _

/-- 列の関係を、漸化式の零始値の列へ移す。 -/
theorem sequenceScalarMap_relation (f : R) (N : ModuleCat.{u} R) (t : N) (x : ℕ → R) :
    sequenceScalarMap R N t (principalReflectionRelation R f x) =
      adicRecurrenceMap f (fun n ↦ Nat.casesOn n 0 (fun k ↦ x k • t)) := by
  funext n
  cases n with
  | zero => simp [sequenceScalarMap, principalReflectionRelation, adicRecurrenceMap, smul_smul]
  | succ n => simp [sequenceScalarMap, principalReflectionRelation, adicRecurrenceMap,
      sub_smul, smul_smul]

/-- 指定した元への延長を、漸化式の一意解の最初の項で構成する。 -/
def principalReflectionLift (f : R) (N : ModuleCat.{u} R) (hN : IsModuleComplete R f N)
    (t : N) : PrincipalReflectionModule R f →ₗ[R] N :=
  (principalReflectionRelation R f).range.liftQ
    ((LinearMap.proj 0).comp ((adicRecurrenceEquiv R f N hN).symm.toLinearMap.comp
      (sequenceScalarMap R N t))) (by
        rintro y ⟨x, rfl⟩
        change (adicRecurrenceEquiv R f N hN).symm
          (sequenceScalarMap R N t (principalReflectionRelation R f x)) 0 = 0
        rw [sequenceScalarMap_relation]
        exact congrFun ((adicRecurrenceEquiv R f N hN).symm_apply_apply _) 0)

@[simp] theorem principalReflectionLift_mk (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (t : N) (x : ℕ → R) :
    principalReflectionLift R f N hN t (principalReflectionMk R f x) =
      (adicRecurrenceEquiv R f N hN).symm (sequenceScalarMap R N t x) 0 := rfl

/-- 延長は標準元を指定された元へ送る。 -/
@[simp] theorem principalReflectionLift_unit (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (t : N) :
    principalReflectionLift R f N hN t (principalReflectionUnit R f) = t := by
  rw [principalReflectionUnit, principalReflectionLift_mk]
  let x : ℕ → N := fun n ↦ Nat.casesOn n t (fun _ ↦ 0)
  have hx : adicRecurrenceEquiv R f N hN x = sequenceScalarMap R N t (sequenceHead R 1) := by
    funext n
    cases n <;> simp [adicRecurrenceEquiv, adicRecurrenceMap, x, sequenceScalarMap, sequenceHead]
  rw [← hx, LinearEquiv.symm_apply_apply]
  rfl

/-- 標準元の像が零なら、完備加群への線形写像は零。 -/
theorem principalReflectionHom_eq_zero (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (g : PrincipalReflectionModule R f →ₗ[R] N)
    (hg : g (principalReflectionUnit R f) = 0) : g = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (principalReflectionRelation R f).range.mkQ_surjective z
  let y : ℕ → N := fun n ↦ g (principalReflectionMk R f (fun k ↦ x (n + k)))
  have hy : adicRecurrenceMap f y = 0 := by
    funext n
    have hd := congrArg g (principalReflectionMk_decomposition R f (fun k ↦ x (n + k)))
    have ht : sequenceTail R (fun k ↦ x (n + k)) = (fun k ↦ x ((n + 1) + k)) := by
      funext k
      change x (n + (k + 1)) = x ((n + 1) + k)
      congr 1
      omega
    rw [ht, map_add, map_smul, map_smul, hg, smul_zero, zero_add] at hd
    change y n - f • y (n + 1) = 0
    exact sub_eq_zero.mpr hd
  have he := ((isModuleComplete_iff_recurrence_bijective R f N).mp hN).injective
    (hy.trans (map_zero _).symm)
  change g (principalReflectionMk R f x) = 0
  simpa [y] using congrFun he 0

/-- この具体的な商から完備加群への線形写像は、標準元での評価と全単射に対応する。 -/
theorem principalReflection_evaluation_bijective (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) :
    Function.Bijective (fun g : PrincipalReflectionModule R f →ₗ[R] N ↦
      g (principalReflectionUnit R f)) := by
  constructor
  · intro g h he
    apply sub_eq_zero.mp
    exact principalReflectionHom_eq_zero R f N hN (g - h) (sub_eq_zero.mpr he)
  · intro t
    exact ⟨principalReflectionLift R f N hN t, principalReflectionLift_unit R f N hN t⟩

end SerrePositivity.DerivedCompletion
