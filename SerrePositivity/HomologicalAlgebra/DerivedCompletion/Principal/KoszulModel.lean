module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Reflection
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.LinearCombination
public import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Milnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure

/-! # 一つの座標の Koszul 完備化の具体的な模型と H⁰ の環

## 概要

一つの座標の Koszul 塔のサイクルと境界を列の組で表し（`PrincipalTowerCycles`）、塔の各段・直積・錐の次数ごとの成分を元の環の列へ同定して微分・差分・標準写像を計算する。加群の反映を環構造の復元の一般定理へ当て、完備化の H⁰ `PrincipalCompletionH0` の環構造と普遍性（`principalCompletionCommRing`・`principalCompletionUnitRingHom`）を与える。導来完備性の係数の制限による判定と、主イデアル商の導来完備性（生成元の正則性は要らない）も与える。

## 方針

次数 −1 と 0 を元の環の列へ同定し、外側の錐の符号を三項模型に合わせる。

## 規約

`PrincipalCompletionH0` は BhattScholze・CLMST が多く使うので名前を変えない（2b の B で定義の中身を見直す候補）。旧 `PrincipalTowerPresentation`・`PrincipalKoszul{Stage, Product, Cone, Unit, Ring}`・`ScalarRestriction`・`PrincipalQuotientComplete`。

## 使われ方

`Principal/Comparisons`、`Pair/*`、`CompletedAlgebraH0`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section PrincipalTowerPresentationPart

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

end PrincipalTowerPresentationPart

section PrincipalKoszulStagePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 元の環を次数0だけに置く複体。 -/
abbrev principalSingle : CochainComplex (ModuleCat.{u} R) ℤ :=
  Adams.oneKoszulUnit

/-- 一座標Koszul塔の次数−1の成分同型。 -/
def principalKoszulStageNegIso (f : R) (n : ℕ) :
    (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X (-1) ≅ ModuleCat.of R R :=
  Adams.oneKoszulXNegOneIso (f ^ n)

/-- 一座標Koszul塔の次数0の成分同型。 -/
def principalKoszulStageZeroIso (f : R) (n : ℕ) :
    (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X 0 ≅ ModuleCat.of R R :=
  Adams.oneKoszulXZeroIso (f ^ n)

/-- 負次数の同型は錐の第1射影。 -/
theorem principalKoszulStageNegIso_hom (f : R) (n : ℕ) :
    (principalKoszulStageNegIso R f n).hom =
      fstX (smulId (f ^ n) (principalSingle R)) (-1) 0 (by decide) ≫
        (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).hom := rfl

/-- 零次数の同型は錐の第2射影。 -/
theorem principalKoszulStageZeroIso_hom (f : R) (n : ℕ) :
    (principalKoszulStageZeroIso R f n).hom =
      sndX (smulId (f ^ n) (principalSingle R)) 0 ≫
        (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).hom := by
  rfl

/-- 一座標の微分は、成分同型の下でfのn乗によるスカラー作用。 -/
theorem principalKoszulStage_d (f : R) (n : ℕ) :
    (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0 ≫
      (principalKoszulStageZeroIso R f n).hom =
    (principalKoszulStageNegIso R f n).hom ≫
      (f ^ n • 𝟙 (ModuleCat.of R R)) := by
  rw [principalKoszulStageZeroIso_hom, principalKoszulStageNegIso_hom]
  change d (smulId (f ^ n) (principalSingle R)) (-1) 0 ≫ _ ≫ _ = _
  rw [← assoc, d_sndX _ (-1) 0 (by decide)]
  simp [principalSingle, smulId]

/-- 負次数の逆同型は錐の第1包含。 -/
theorem principalKoszulStageNegIso_inv (f : R) (n : ℕ) :
    (principalKoszulStageNegIso R f n).inv =
      (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
        inlX (smulId (f ^ n) (principalSingle R)) 0 (-1) (by decide) := rfl

/-- 零次数の逆同型は錐の第2包含。 -/
theorem principalKoszulStageZeroIso_inv (f : R) (n : ℕ) :
    (principalKoszulStageZeroIso R f n).inv =
      (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
        inrX (smulId (f ^ n) (principalSingle R)) 0 := by
  rfl

/-- 負次数の遷移はf倍である。 -/
theorem principalKoszulStageNeg_transition (f : R) (n : ℕ) :
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1) ≫
      (principalKoszulStageNegIso R f n).hom =
    (principalKoszulStageNegIso R f (n + 1)).hom ≫
      (f • 𝟙 (ModuleCat.of R R)) := by
  apply (cancel_epi (principalKoszulStageNegIso R f (n + 1)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  rw [principalKoszulStageNegIso_inv]
  change (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
    inlX (smulId (f ^ (n + 1)) (principalSingle R)) 0 (-1) (by decide) ≫
      (mapArrowHom (smulId (f ^ (n + 1)) (principalSingle R))
        (smulId (f ^ n) (principalSingle R)) (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk (f • 𝟙 _) (𝟙 _) (by
          simp [smulId, pow_succ, smul_smul, koszulComplex, principalSingle]))).f (-1) ≫
          (principalKoszulStageNegIso R f n).hom = _
  simp [koszulComplex, mapArrowHom, principalSingle,
    Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft,
    inrCompHomotopy_hom, principalKoszulStageNegIso_hom, smulId]

/-- 零次数の遷移は恒等写像である。 -/
theorem principalKoszulStageZero_transition (f : R) (n : ℕ) :
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0 ≫
      (principalKoszulStageZeroIso R f n).hom =
    (principalKoszulStageZeroIso R f (n + 1)).hom := by
  apply (cancel_epi (principalKoszulStageZeroIso R f (n + 1)).inv).mp
  rw [Iso.inv_hom_id, principalKoszulStageZeroIso_inv]
  change (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
    inrX (smulId (f ^ (n + 1)) (principalSingle R)) 0 ≫
      (mapArrowHom (smulId (f ^ (n + 1)) (principalSingle R))
        (smulId (f ^ n) (principalSingle R)) (fun j ↦ ⟨j - 1, by simp⟩)
        (Arrow.homMk (f • 𝟙 _) (𝟙 _) (by
          simp [smulId, pow_succ, smul_smul, koszulComplex, principalSingle]))).f 0 ≫
          (principalKoszulStageZeroIso R f n).hom = _
  simp [koszulComplex, mapArrowHom,
    principalKoszulStageZeroIso_hom, principalSingle]

end SerrePositivity.DerivedCompletion

end PrincipalKoszulStagePart

section PrincipalKoszulProductPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]

/-- 一座標Koszul塔の負次数の直積を環の列へ同定する。 -/
def principalKoszulProductNegEquiv (f : R) :
    (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1) ≃ₗ[R] (ℕ → R) :=
  (complexProductDegreeEquiv R _ (-1)).trans
    (LinearEquiv.piCongrRight (fun n ↦ (principalKoszulStageNegIso R f n).toLinearEquiv))

/-- 一座標Koszul塔の零次数の直積を環の列へ同定する。 -/
def principalKoszulProductZeroEquiv (f : R) :
    (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X 0 ≃ₗ[R] (ℕ → R) :=
  (complexProductDegreeEquiv R _ 0).trans
    (LinearEquiv.piCongrRight (fun n ↦ (principalKoszulStageZeroIso R f n).toLinearEquiv))

@[simp] theorem principalKoszulProductNegEquiv_apply (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1)) (n : ℕ) :
    principalKoszulProductNegEquiv R f x n =
      (principalKoszulStageNegIso R f n).hom
        ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x) := by
  simp [principalKoszulProductNegEquiv]
  rfl

@[simp] theorem principalKoszulProductZeroEquiv_apply (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X 0) (n : ℕ) :
    principalKoszulProductZeroEquiv R f x n =
      (principalKoszulStageZeroIso R f n).hom
        ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0 x) := by
  simp [principalKoszulProductZeroEquiv]
  rfl

/-- 直積の微分は、各座標でfの冪を掛ける写像。 -/
theorem principalKoszulProduct_d (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1)) :
    principalKoszulProductZeroEquiv R f
      ((piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).d (-1) 0 x) =
    principalPowerMap R f (principalKoszulProductNegEquiv R f x) := by
  ext n
  rw [principalKoszulProductZeroEquiv_apply]
  have h := congrArg (fun g ↦ g.hom x)
    ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).comm (-1) 0)
  change (powerKoszulTower R (fun _ : Fin 1 ↦ f) n).d (-1) 0
    ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x) =
      (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0
        ((piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).d (-1) 0 x) at h
  rw [← h]
  have hd := congrArg (fun g ↦ g.hom ((Pi.π (powerKoszulTower R
    (fun _ : Fin 1 ↦ f)) n).f (-1) x)) (principalKoszulStage_d R f n)
  simpa [principalPowerMap, principalKoszulProductNegEquiv_apply, smul_eq_mul] using hd

/-- 負次数の直積差分はfによる漸化式。 -/
theorem principalKoszulProductNeg_difference (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X (-1)) :
    principalKoszulProductNegEquiv R f
      ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
        (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f (-1) x) =
    adicRecurrenceMap f (principalKoszulProductNegEquiv R f x) := by
  ext n
  rw [principalKoszulProductNegEquiv_apply]
  have h := congrArg (fun g ↦ (g.f (-1)).hom x)
    (complexTowerDifference_projection R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f)) n)
  change (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1)
    ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f (-1) x) =
    (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x -
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f (-1)
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) (n + 1)).f (-1) x) at h
  rw [h, map_sub]
  have ht := congrArg (fun g ↦ g.hom ((Pi.π (powerKoszulTower R
    (fun _ : Fin 1 ↦ f)) (n + 1)).f (-1) x))
      (principalKoszulStageNeg_transition R f n)
  simpa [adicRecurrenceMap, principalKoszulProductNegEquiv_apply, smul_eq_mul] using
    congrArg (fun y : R ↦ (principalKoszulStageNegIso R f n).hom
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f (-1) x) - y) ht

/-- 零次数の直積差分は恒等遷移による漸化式。 -/
theorem principalKoszulProductZero_difference (f : R)
    (x : (piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X 0) :
    principalKoszulProductZeroEquiv R f
      ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
        (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f 0 x) =
    adicRecurrenceMap (1 : R) (principalKoszulProductZeroEquiv R f x) := by
  ext n
  rw [principalKoszulProductZeroEquiv_apply]
  have h := congrArg (fun g ↦ (g.f 0).hom x)
    (complexTowerDifference_projection R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f)) n)
  change (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0
    ((complexTowerDifference R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
    (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f 0 x) =
    (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0 x -
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f) n).f 0
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) (n + 1)).f 0 x) at h
  rw [h, map_sub]
  have ht := congrArg (fun g ↦ g.hom ((Pi.π (powerKoszulTower R
    (fun _ : Fin 1 ↦ f)) (n + 1)).f 0 x))
      (principalKoszulStageZero_transition R f n)
  simpa [adicRecurrenceMap, principalKoszulProductZeroEquiv_apply] using
    congrArg (fun y : R ↦ (principalKoszulStageZeroIso R f n).hom
      ((Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0 x) - y) ht

/-- 直積も、一座標Koszul複体の範囲外では零。 -/
theorem principalKoszulProduct_isZero (f : R) (i : ℤ) (hi : i < -1 ∨ 0 < i) :
    IsZero ((piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))).X i) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ (complexProductDegreeEquiv R _ i).injective ?_⟩
  funext n
  have hn : IsZero ((powerKoszulTower R (fun _ : Fin 1 ↦ f) n).X i) := by
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt _ i (by simpa using hi)
    · exact koszulComplex_isZero_X_of_pos _ i hi
  exact (ModuleCat.isZero_iff_subsingleton.mp hn).elim _ _

end SerrePositivity.DerivedCompletion

end PrincipalKoszulProductPart

section PrincipalKoszulConePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- 一座標Koszul塔の実際の直積。 -/
abbrev principalKoszulProduct (f : R) := piObj (powerKoszulTower R (fun _ : Fin 1 ↦ f))
/-- 一座標Koszul塔の実際の差分写像。 -/
abbrev principalKoszulDifference (f : R) := complexTowerDifference R
  (powerKoszulTower R (fun _ : Fin 1 ↦ f)) (powerKoszulTransition R (fun _ : Fin 1 ↦ f))

/-- 実際の完備化複体の次数−1を列へ同定する。 -/
def principalCompletionNegEquiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X (-1) ≃ₗ[R] (ℕ → R) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) (-1) (-2) (by norm_num)).toLinearEquiv.trans
    ((moduleConeFstIso (principalKoszulDifference R f) (-2) (-1) (by decide)
      (principalKoszulProduct_isZero R f (-2) (Or.inl (by norm_num)))).toLinearEquiv.trans
        (principalKoszulProductNegEquiv R f))

/-- 実際の完備化複体の次数0を列の組へ同定する。 -/
def principalCompletionZeroEquiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0 ≃ₗ[R] ((ℕ → R) × (ℕ → R)) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 0 (-1) (by norm_num)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (principalKoszulDifference R f) (-1) 0 (by decide) ≪≫ₗ
      (principalKoszulProductZeroEquiv R f).prodCongr
        (principalKoszulProductNegEquiv R f) ≪≫ₗ
          (LinearEquiv.refl R (ℕ → R)).prodCongr (LinearEquiv.neg R)

/-- 実際の完備化複体の次数1を列へ同定する。 -/
def principalCompletionOneEquiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 1 ≃ₗ[R] (ℕ → R) :=
  (CochainComplex.shiftFunctorObjXIso _ (-1) 1 0 (by norm_num)).toLinearEquiv ≪≫ₗ
    (moduleConeSndIso (principalKoszulDifference R f) 0 1 rfl
      (principalKoszulProduct_isZero R f 1 (Or.inr (by norm_num)))).toLinearEquiv ≪≫ₗ
        principalKoszulProductZeroEquiv R f ≪≫ₗ LinearEquiv.neg R

@[simp] theorem principalCompletionNegEquiv_apply (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X (-1)) :
    principalCompletionNegEquiv R f x = principalKoszulProductNegEquiv R f
      (fstX (principalKoszulDifference R f) (-2) (-1) (by decide) x) := rfl

@[simp] theorem principalCompletionZeroEquiv_fst (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0) :
    (principalCompletionZeroEquiv R f x).1 = principalKoszulProductZeroEquiv R f
      (fstX (principalKoszulDifference R f) (-1) 0 (by decide) x) := rfl

@[simp] theorem principalCompletionZeroEquiv_snd (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0) :
    (principalCompletionZeroEquiv R f x).2 = -principalKoszulProductNegEquiv R f
      (sndX (principalKoszulDifference R f) (-1) x) := rfl

@[simp] theorem principalCompletionOneEquiv_apply (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 1) :
    principalCompletionOneEquiv R f x = -principalKoszulProductZeroEquiv R f
      (sndX (principalKoszulDifference R f) 0 x) := rfl

/-- 一段シフトした実際の微分の符号。 -/
theorem principalCompletion_d_eq (f : R) (i j : ℤ) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).d i j =
      -d (principalKoszulDifference R f) (i + -1) (j + -1) := by
  change (-1 : ℤ).negOnePow • _ = -_
  simp
  rfl

/-- 次数−1から0への微分は、具体的三項モデルの境界写像。 -/
theorem principalCompletion_d_neg (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X (-1)) :
    principalCompletionZeroEquiv R f
      ((koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).d (-1) 0 x) =
    principalTowerBoundaryPair R f (principalCompletionNegEquiv R f x) := by
  apply Prod.ext
  · rw [principalCompletionZeroEquiv_fst, principalCompletionNegEquiv_apply]
    have h := congrArg (fun g ↦ g.hom x)
      (d_fstX (principalKoszulDifference R f) (-2) (-1) 0 (by decide) (by decide))
    rw [principalCompletion_d_eq]
    change principalKoszulProductZeroEquiv R f
      (fstX (principalKoszulDifference R f) (-1) 0 (by decide)
        (-d (principalKoszulDifference R f) (-2) (-1) x)) = _
    rw [map_neg, map_neg]
    change -principalKoszulProductZeroEquiv R f
      (fstX (principalKoszulDifference R f) (-1) 0 (by decide)
        (d (principalKoszulDifference R f) (-2) (-1) x)) = _
    change fstX (principalKoszulDifference R f) (-1) 0 (by decide)
      (d (principalKoszulDifference R f) (-2) (-1) x) =
        -(principalKoszulProduct R f).d (-1) 0
          (fstX (principalKoszulDifference R f) (-2) (-1) (by decide) x) at h
    rw [h, map_neg, neg_neg, principalKoszulProduct_d]
    rfl
  · rw [principalCompletionZeroEquiv_snd, principalCompletionNegEquiv_apply]
    have h := congrArg (fun g ↦ g.hom x)
      (d_sndX (principalKoszulDifference R f) (-2) (-1) (by decide))
    have hz : sndX (principalKoszulDifference R f) (-2) x = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp
        (principalKoszulProduct_isZero R f (-2) (Or.inl (by norm_num)))).elim _ _
    rw [principalCompletion_d_eq]
    change -principalKoszulProductNegEquiv R f
      (sndX (principalKoszulDifference R f) (-1)
        (-d (principalKoszulDifference R f) (-2) (-1) x)) = _
    rw [map_neg, map_neg, neg_neg]
    change sndX (principalKoszulDifference R f) (-1)
      (d (principalKoszulDifference R f) (-2) (-1) x) =
        (principalKoszulDifference R f).f (-1)
          (fstX (principalKoszulDifference R f) (-2) (-1) (by decide) x) +
            (principalKoszulProduct R f).d (-2) (-1)
              (sndX (principalKoszulDifference R f) (-2) x) at h
    rw [hz, map_zero, add_zero] at h
    rw [h, principalKoszulProductNeg_difference]
    rfl

/-- 次数0から1への微分は、具体的三項モデルのサイクル条件。 -/
theorem principalCompletion_d_zero (f : R)
    (x : (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).X 0) :
    principalCompletionOneEquiv R f
      ((koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).d 0 1 x) =
    principalTowerObstruction R f (principalCompletionZeroEquiv R f x) := by
  rw [principalCompletionOneEquiv_apply]
  rw [principalCompletion_d_eq]
  change -principalKoszulProductZeroEquiv R f
    (sndX (principalKoszulDifference R f) 0
      (-d (principalKoszulDifference R f) (-1) 0 x)) = _
  rw [map_neg, map_neg, neg_neg]
  have h := congrArg (fun g : (CochainComplex.mappingCone
    (principalKoszulDifference R f)).X (-1) ⟶ (principalKoszulProduct R f).X 0 ↦ g.hom x)
    (d_sndX (principalKoszulDifference R f) (-1) 0 (by decide))
  change sndX (principalKoszulDifference R f) 0
    (d (principalKoszulDifference R f) (-1) 0 x) =
      (principalKoszulDifference R f).f 0
        (fstX (principalKoszulDifference R f) (-1) 0 (by decide) x) +
          (principalKoszulProduct R f).d (-1) 0
            (sndX (principalKoszulDifference R f) (-1) x) at h
  rw [h, map_add, principalKoszulProductZero_difference, principalKoszulProduct_d]
  simp [principalTowerObstruction, principalCompletionZeroEquiv_fst,
    principalCompletionZeroEquiv_snd, sub_neg_eq_add]

/-- 実際のKoszul完備化の短複体と、具体的な三項モデルの同型。 -/
def principalCompletionShortComplexIso (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).sc 0 ≅
      principalTowerShortComplex R f :=
  (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).isoSc' (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by decide))
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)) ≪≫
      ShortComplex.isoMk (principalCompletionNegEquiv R f).toModuleIso
        (principalCompletionZeroEquiv R f).toModuleIso
        (principalCompletionOneEquiv R f).toModuleIso
        (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact (principalCompletion_d_neg R f x).symm)
        (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact (principalCompletion_d_zero R f x).symm)

/-- 実際のKoszul完備化のH⁰を、一座標の反射加群へ同定する。 -/
def principalCompletionH0Equiv (f : R) :
    (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).homology 0 ≃ₗ[R]
      PrincipalReflectionModule R f :=
  (ShortComplex.homologyMapIso (principalCompletionShortComplexIso R f)).toLinearEquiv.trans
    (principalTowerHomologyEquiv R f)

end SerrePositivity.DerivedCompletion

end PrincipalKoszulConePart

section PrincipalKoszulUnitPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

/-- Koszulの標準包含は、零次数の成分同型を通じて元の元へ戻る。 -/
theorem principalKoszulInclusion_zero (f : R) (n : ℕ) :
    (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv ≫
      (koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n)).f 0 ≫
        (principalKoszulStageZeroIso R f n).hom = 𝟙 (ModuleCat.of R R) := by
  simp [koszulComplexInclusion, principalKoszulStageZeroIso_hom, koszulComplex,
    CochainComplex.mappingCone.inr, HomologicalComplex.homotopyCofiber.inr_f]

/-- ホモトピー逆極限への標準持ち上げの第2成分は、各次数で零。 -/
theorem complexTowerHomotopyLimitLift_snd_component
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) (i : ℤ) :
    (complexTowerHomotopyLimitLift R K t P g hg).f i ≫
      sndX (complexTowerDifference R K t) (i + -1) = 0 := by
  have h := congrArg (fun γ ↦ γ.v i (i + -1) rfl)
    (complexTowerHomotopyLimitLift_snd R K t P g hg)
  simp only [CochainComplex.HomComplex.Cochain.comp_v
    (n₁ := -1) (n₂ := 0) (n₁₂ := -1) _ _ _ i (i + -1) (i + -1) rfl (by omega)] at h
  change ((CochainComplex.HomComplex.Cochain.ofHom
    (complexTowerHomotopyLimitLift R K t P g hg)).rightUnshift (-1) (zero_add _)).v
      i (i + -1) rfl ≫
        (CochainComplex.mappingCone.snd (complexTowerDifference R K t)).v
          (i + -1) (i + -1) (add_zero _) = 0 at h
  rw [CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ i (i + -1) rfl
    i (add_zero i)] at h
  simpa [CochainComplex.mappingCone.snd, CochainComplex.shiftFunctorObjXIso] using h

/-- 正規化されたホモトピー逆極限射影の零次数成分。 -/
theorem principalCompletionProjection_zero (f : R) :
    (complexTowerProjection R (powerKoszulTower R (fun _ : Fin 1 ↦ f))
      (powerKoszulTransition R (fun _ : Fin 1 ↦ f))).f 0 =
    fstX (principalKoszulDifference R f) (-1) 0 (by decide) := by
  simp [complexTowerProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.mappingCone.fst]

/-- 一座標完備化の標準写像の第1座標は定数列。 -/
theorem principalCompletionZeroEquiv_unit_fst (f r : R) :
    (principalCompletionZeroEquiv R f
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).1 =
      fun _ ↦ r := by
  ext n
  rw [principalCompletionZeroEquiv_fst, principalKoszulProductZeroEquiv_apply]
  have h := congrArg (fun g ↦ (g.f 0).hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))
      (koszulCompletionUnit_comp_projection R (fun _ : Fin 1 ↦ f) n)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    principalCompletionProjection_zero] at h
  change (Pi.π (powerKoszulTower R (fun _ : Fin 1 ↦ f)) n).f 0
    (fstX (principalKoszulDifference R f) (-1) 0 (by decide)
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))) =
      (koszulComplexInclusion R (fun _ : Fin 1 ↦ f ^ n)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r) at h
  rw [h]
  exact congrArg (fun g ↦ g.hom r) (principalKoszulInclusion_zero R f n)

/-- 一座標完備化の標準写像の第2座標は零。 -/
theorem principalCompletionZeroEquiv_unit_snd (f r : R) :
    (principalCompletionZeroEquiv R f
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r))).2 = 0 := by
  rw [principalCompletionZeroEquiv_snd]
  have h : (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0 ≫
      sndX (principalKoszulDifference R f) (-1) = 0 := by
    dsimp only [koszulCompletionUnit, complexTowerCompatibleLift]
    apply complexTowerHomotopyLimitLift_snd_component
  have hr := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) h
  change sndX (principalKoszulDifference R f) (-1)
    ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = 0 at hr
  rw [hr, map_zero, neg_zero]

/-- 標準包含は定数列と零列の組へ送られる。 -/
theorem principalCompletionZeroEquiv_unit (f r : R) :
    principalCompletionZeroEquiv R f
      ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
        ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) =
      (fun _ ↦ r, 0) :=
  Prod.ext (principalCompletionZeroEquiv_unit_fst R f r)
    (principalCompletionZeroEquiv_unit_snd R f r)

/-- 単一複体から三項モデルへの標準短複体写像。 -/
def principalCompletionUnitShortMap (f : R) :
    (principalSingle R).sc 0 ⟶ principalTowerShortComplex R f :=
  (HomologicalComplex.shortComplexFunctor _ _ 0).map
    (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) ≫
      (principalCompletionShortComplexIso R f).hom

/-- 標準短複体写像は、サイクルとしての標準元も保つ。 -/
theorem principalCompletionUnitShortMap_cycles (f r : R) :
    ShortComplex.cyclesMap (principalCompletionUnitShortMap R f)
      ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r) =
    (principalTowerShortComplex R f).moduleCatCyclesIso.inv
      (principalTowerConstantCycle R f r) := by
  apply (ModuleCat.mono_iff_injective (principalTowerShortComplex R f).iCycles).mp
    inferInstance
  have h := congrArg (fun g ↦ g.hom
    ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r))
      (ShortComplex.cyclesMap_i (principalCompletionUnitShortMap R f))
  change (principalTowerShortComplex R f).iCycles
    (ShortComplex.cyclesMap (principalCompletionUnitShortMap R f)
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv r)) =
      (principalCompletionUnitShortMap R f).τ₂
        ((principalSingle R).iCycles 0
          ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
            (ModuleCat.of R R)).inv r)) at h
  rw [h]
  have hsrc := congrArg (fun g ↦ g.hom r)
    (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles
      (ComplexShape.up ℤ) 0 (ModuleCat.of R R))
  have htgt := congrArg (fun g ↦ g.hom (principalTowerConstantCycle R f r))
    (principalTowerShortComplex R f).moduleCatCyclesIso_inv_iCycles
  change (principalTowerShortComplex R f).iCycles
    ((principalTowerShortComplex R f).moduleCatCyclesIso.inv
      (principalTowerConstantCycle R f r)) = (principalTowerConstantCycle R f r).val at htgt
  rw [htgt]
  change (principalSingle R).iCycles 0
    ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv r) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r at hsrc
  change (principalCompletionUnitShortMap R f).τ₂
    ((principalSingle R).iCycles 0
      ((HomologicalComplex.singleObjCyclesSelfIso _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [hsrc]
  change principalCompletionZeroEquiv R f
    ((koszulCompletionUnit R (fun _ : Fin 1 ↦ f)).f 0
      ((HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).inv r)) = _
  rw [principalCompletionZeroEquiv_unit, principalTowerConstantCycle_val]

/-- H⁰の比較同型は、既存の標準写像を列の商の標準写像へ送る。 -/
theorem principalCompletionH0Equiv_unit (f r : R) :
    principalCompletionH0Equiv R f
      (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) r) =
    principalReflectionMk R f (sequenceHead R r) := by
  let c : (principalSingle R).cycles 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv r
  have hrep : (HomologicalComplex.singleObjHomologySelfIso _ 0
      (ModuleCat.of R R)).inv r = (principalSingle R).homologyπ 0 c := by
    have h : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv ≫ (principalSingle R).homologyπ 0 := by
      rw [← HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact congrArg (fun g ↦ g.hom r) h
  have hn := congrArg (fun g ↦ g.hom c)
    (ShortComplex.homologyπ_naturality (principalCompletionUnitShortMap R f))
  change ShortComplex.homologyMap (principalCompletionUnitShortMap R f)
    ((principalSingle R).homologyπ 0 c) =
      (principalTowerShortComplex R f).homologyπ
        (ShortComplex.cyclesMap (principalCompletionUnitShortMap R f) c) at hn
  rw [show ShortComplex.cyclesMap (principalCompletionUnitShortMap R f) c =
    (principalTowerShortComplex R f).moduleCatCyclesIso.inv
      (principalTowerConstantCycle R f r) from principalCompletionUnitShortMap_cycles R f r] at hn
  change principalTowerHomologyEquiv R f
    (ShortComplex.homologyMap (principalCompletionShortComplexIso R f).hom
      (HomologicalComplex.homologyMap (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) 0
        ((HomologicalComplex.singleObjHomologySelfIso _ 0 (ModuleCat.of R R)).inv r))) = _
  rw [hrep]
  have hcomp : ShortComplex.homologyMap (principalCompletionUnitShortMap R f) =
      HomologicalComplex.homologyMap (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) 0 ≫
        ShortComplex.homologyMap (principalCompletionShortComplexIso R f).hom :=
    ShortComplex.homologyMap_comp _ _
  rw [hcomp] at hn
  change ShortComplex.homologyMap (principalCompletionShortComplexIso R f).hom
    (HomologicalComplex.homologyMap (koszulCompletionUnit R (fun _ : Fin 1 ↦ f)) 0
      ((principalSingle R).homologyπ 0 c)) = principalTowerHomologyUnit R f r at hn
  rw [hn, principalTowerHomologyEquiv_unit]

/-- 実際の一座標Koszul完備化のH⁰は、標準元について完備加群への反射。 -/
theorem principalCompletionH0_isCompleteModuleReflection (f : R) :
    IsCompleteModuleReflection R (fun _ : Fin 1 ↦ f)
      ((koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).homology 0)
      (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) 1) :=
  (principalReflection_isCompleteModuleReflection R f).of_linearEquiv R
    (principalCompletionH0Equiv R f).symm (by
      apply (principalCompletionH0Equiv R f).injective
      rw [LinearEquiv.apply_symm_apply, principalCompletionH0Equiv_unit]
      rfl)

end SerrePositivity.DerivedCompletion

end PrincipalKoszulUnitPart

section PrincipalKoszulRingPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 実際の一座標Koszul完備化の零次ホモロジー。 -/
abbrev PrincipalCompletionH0 (f : R) :=
  (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).homology 0

/-- 元の加法群・加群と両立する、実際のH⁰上の可換環構造。 -/
@[instance_reducible] def principalCompletionCommRing (f : R) :
    CommRing (PrincipalCompletionH0 R f) :=
  (principalCompletionH0_isCompleteModuleReflection R f).commRing

/-- 元のスカラー作用を保つ、実際のH⁰のR代数構造。 -/
@[instance_reducible] def principalCompletionAlgebra (f : R) :
    letI := principalCompletionCommRing R f; Algebra R (PrincipalCompletionH0 R f) :=
  (principalCompletionH0_isCompleteModuleReflection R f).algebra

/-- 既存のH⁰標準写像を環準同型として実現する。 -/
def principalCompletionUnitRingHom (f : R) :
    letI := principalCompletionCommRing R f; R →+* PrincipalCompletionH0 R f :=
  (principalCompletionH0_isCompleteModuleReflection R f).unitRingHom

/-- 環としての標準写像は、既存のKoszul完備化のH⁰標準写像と一致する。 -/
theorem principalCompletionUnitRingHom_apply (f r : R) :
    principalCompletionUnitRingHom R f r =
      koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) r :=
  (principalCompletionH0_isCompleteModuleReflection R f).unitRingHom_eq_linearMap
    (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f)) rfl r

/-- 実際のH⁰は、fについて導来完備なR加群。 -/
theorem principalCompletionH0_isModuleComplete (f : R) :
    IsModuleComplete R f (PrincipalCompletionH0 R f) :=
  (principalCompletionH0_isCompleteModuleReflection R f).isComplete 0

/-- 実際のH⁰から導来完備なR代数への延長は一意。 -/
theorem principalCompletion_existsUnique_algHom (f : R)
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsModuleComplete R f (ModuleCat.of R T)) :
    letI := principalCompletionCommRing R f
    letI := principalCompletionAlgebra R f
    ∃! _g : PrincipalCompletionH0 R f →ₐ[R] T, True :=
  (principalCompletionH0_isCompleteModuleReflection R f).existsUnique_algHom T (fun _ ↦ hT)

/-- 任意の環準同型は、標準写像から導来完備な離散環へ一意に延長する。 -/
theorem principalCompletion_existsUnique_ringHom (f : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hT : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T)) :
    letI := principalCompletionCommRing R f
    ∃! h : PrincipalCompletionH0 R f →+* T,
      h.comp (principalCompletionUnitRingHom R f) = g := by
  let := g.toAlgebra
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  obtain ⟨h, _, hu⟩ := principalCompletion_existsUnique_algHom R f T hT
  refine ⟨h.toRingHom, ?_, ?_⟩
  · ext r
    exact h.commutes r
  · intro k hk
    let k' : PrincipalCompletionH0 R f →ₐ[R] T :=
      { k with commutes' := fun r ↦ congrArg (fun m : R →+* T ↦ m r) hk }
    exact congrArg AlgHom.toRingHom (hu k' trivial)

end SerrePositivity.DerivedCompletion

end PrincipalKoszulRingPart

section ScalarRestrictionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- 代数写像に沿う係数制限は、対応する元についての導来完備性を保ち、反映する。 -/
theorem isModuleComplete_algebraMap_iff (f : R) (M : Type u)
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    IsModuleComplete S (algebraMap R S f) (ModuleCat.of S M) ↔
      IsModuleComplete R f (ModuleCat.of R M) := by
  rw [isModuleComplete_iff_recurrence_bijective, isModuleComplete_iff_recurrence_bijective]
  have he : (fun x : ℕ → M ↦ adicRecurrenceMap (algebraMap R S f) x) =
      fun x : ℕ → M ↦ adicRecurrenceMap f x := by
    funext x n
    simp [adicRecurrenceMap]
  exact (congrArg Function.Bijective he).to_iff

omit [Algebra R S] in
/-- 合成環準同型による作用の下で、対応する元の完備性を比較する。 -/
theorem isModuleComplete_ringHom_comp_iff (T : Type u) [CommRing T]
    (u : R →+* S) (v : S →+* T) (f : R) :
    (letI := v.toAlgebra;
      IsModuleComplete S (u f) (ModuleCat.of S T)) ↔
    (letI := (v.comp u).toAlgebra;
      IsModuleComplete R f (ModuleCat.of R T)) := by
  let := v.toAlgebra
  let := (v.comp u).toAlgebra
  rw [isModuleComplete_iff_recurrence_bijective, isModuleComplete_iff_recurrence_bijective]
  rfl

/-- 別の元に関する主元反射は、既にある導来完備性を保つ。 -/
theorem principalReflection_isModuleComplete_of_other (f : R) (d : S)
    (hS : IsModuleComplete R f (ModuleCat.of R S)) :
    let := Module.compHom (PrincipalReflectionModule S d) (algebraMap R S)
    IsModuleComplete R f (ModuleCat.of R (PrincipalReflectionModule S d)) := by
  let := Module.compHom (PrincipalReflectionModule S d) (algebraMap R S)
  have hP := isModuleComplete_pi R f (fun _ : ℕ ↦ ModuleCat.of R S) (fun _ ↦ hS)
  let g := (principalReflectionRelation S d).restrictScalars R
  have hQ := isModuleComplete_coker R f g hP hP
  let e : ((ℕ → S) ⧸ g.range) ≃ₗ[R] PrincipalReflectionModule S d :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          have he : ((algebraMap R S r) • x : ℕ → S) = r • x := by
            ext n
            simp [Algebra.smul_def]
          exact congrArg (fun z : ℕ → S ↦ (principalReflectionRelation S d).range.mkQ z) he.symm }
  exact isModuleComplete_of_linearEquiv R f (ModuleCat.of R ((ℕ → S) ⧸ g.range))
    (ModuleCat.of R (PrincipalReflectionModule S d)) e hQ

/-- 実際の主元Koszul完備化のH⁰も、別の元についての導来完備性を保つ。 -/
theorem principalCompletionH0_isModuleComplete_of_other (f : R) (d : S)
    (hS : IsModuleComplete R f (ModuleCat.of R S)) :
    letI := Module.compHom (PrincipalCompletionH0 S d) (algebraMap R S)
    IsModuleComplete R f (ModuleCat.of R (PrincipalCompletionH0 S d)) := by
  let _ : Module R (PrincipalCompletionH0 S d) :=
    Module.compHom (PrincipalCompletionH0 S d) (algebraMap R S)
  let _ : Module R (PrincipalReflectionModule S d) :=
    Module.compHom (PrincipalReflectionModule S d) (algebraMap R S)
  have hQ := principalReflection_isModuleComplete_of_other R S f d hS
  let e : PrincipalCompletionH0 S d ≃ₗ[R] PrincipalReflectionModule S d :=
    { toFun := principalCompletionH0Equiv S d
      invFun := (principalCompletionH0Equiv S d).symm
      left_inv := (principalCompletionH0Equiv S d).left_inv
      right_inv := (principalCompletionH0Equiv S d).right_inv
      map_add' := (principalCompletionH0Equiv S d).map_add
      map_smul' := fun r x ↦ (principalCompletionH0Equiv S d).map_smul (algebraMap R S r) x }
  exact isModuleComplete_of_linearEquiv R f
    (ModuleCat.of R (PrincipalReflectionModule S d))
    (ModuleCat.of R (PrincipalCompletionH0 S d)) e.symm hQ

end SerrePositivity.DerivedCompletion

end ScalarRestrictionPart

section PrincipalQuotientCompletePart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 主イデアルは生成元の乗法写像の像。 -/
theorem mulLeft_range_eq_span (d : R) :
    (LinearMap.mulLeft R d).range = (Ideal.span {d} : Submodule R R) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Ideal.mem_span_singleton, dvd_def]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

/-- 主イデアル商を元の環の加群と見た導来完備性。 -/
theorem isModuleComplete_principal_quotient_restrict (f d : R)
    (hR : IsModuleComplete R f (ModuleCat.of R R)) :
    IsModuleComplete R f (ModuleCat.of R (R ⧸ Ideal.span {d})) := by
  have h := isModuleComplete_coker R f (LinearMap.mulLeft R d) hR hR
  rw [mulLeft_range_eq_span] at h
  exact h

/-- 主イデアル商自身の環作用に関する導来完備性。 -/
theorem isModuleComplete_principal_quotient (f d : R)
    (hR : IsModuleComplete R f (ModuleCat.of R R)) :
    IsModuleComplete (R ⧸ Ideal.span {d}) (Ideal.Quotient.mk (Ideal.span {d}) f)
      (ModuleCat.of (R ⧸ Ideal.span {d}) (R ⧸ Ideal.span {d})) := by
  exact (isModuleComplete_algebraMap_iff R (R ⧸ Ideal.span {d}) f
    (R ⧸ Ideal.span {d})).mpr (isModuleComplete_principal_quotient_restrict R f d hR)

/-- pの自然数像を使う公開形。 -/
theorem isModuleComplete_principal_quotient_natCast (p : ℕ) (d : R)
    (hR : IsModuleComplete R (p : R) (ModuleCat.of R R)) :
    IsModuleComplete (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d})
      (ModuleCat.of (R ⧸ Ideal.span {d}) (R ⧸ Ideal.span {d})) := by
  simpa only [map_natCast] using isModuleComplete_principal_quotient R (p : R) d hR

end SerrePositivity.DerivedCompletion

end PrincipalQuotientCompletePart
