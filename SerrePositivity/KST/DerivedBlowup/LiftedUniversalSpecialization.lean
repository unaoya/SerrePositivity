module

public import SerrePositivity.KST.DerivedBlowup.UniversalSpecialization
public import SerrePositivity.KST.DerivedBlowup.UniversalKoszulResolution
public import SerrePositivity.KST.DerivedBlowup.ChartBaseChangeDGFunctor
public import Mathlib.Algebra.Ring.ULift

/-!
概要：KST Def3.1・Lemma3.6 の普遍底変更を任意宇宙の係数環へ適用する。
方針：普遍基底を ULift で係数環と同じ宇宙へ移し、既存の同一宇宙 dg 底変更 API を使う。
規約：ULift は環同型であり、追加の数学的仮定ではない。
使われ方：普遍チャートの dg 解消を任意係数へ底変更する際の宇宙の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：係数環の宇宙へ持ち上げた普遍基底。
方針：整数上の普遍多項式環に ULift を施す。
規約：KST Def3.1。使われ方：同一宇宙の dg 底変更 API の入力。 -/
abbrev LiftedUniversalBase (r : ℕ) := ULift.{u} (UniversalBase (Fin (r + 1)))

/-- 概要：持ち上げた普遍基底の生成元族。
方針：各独立変数を ULift.up で送る。
規約：KST Def3.1。使われ方：持ち上げた普遍チャートの Koszul 関係式。 -/
def liftedUniversalCoefficients (r : ℕ) : Fin (r + 1) → LiftedUniversalBase.{u} r :=
  fun j => ULift.up (MvPolynomial.X j)

/-- 概要：持ち上げた普遍基底を指定係数へ特殊化する環射。
方針：ULift の環同型を元へ戻して普遍評価を合成する。
規約：KST Def3.1。使われ方：任意宇宙での普遍係数代入。 -/
def liftedUniversalSpecialization (a : Fin (r + 1) → R) : LiftedUniversalBase.{u} r →+* R :=
  (universalSpecialization a).comp ULift.ringEquiv.toRingHom

/-- 概要：持ち上げた普遍生成元の像は指定係数。
方針：ULift の往復と普遍評価の生成元公式。
規約：KST Def3.1。使われ方：チャート関係式の特殊化。 -/
@[simp] theorem liftedUniversalSpecialization_generator (a : Fin (r + 1) → R)
    (j : Fin (r + 1)) :
    liftedUniversalSpecialization a (liftedUniversalCoefficients r j) = a j := by
  change universalSpecialization a (MvPolynomial.X j) = a j
  exact universalSpecialization_X a j

/-- 概要：持ち上げた普遍チャートの係数特殊化代数射。
方針：係数の代数準同型を多項式環へ写す。
規約：KST Def3.1。使われ方：既存のチャート dg 底変更関手への入力。 -/
def liftedUniversalChartSpecializationAlgHom (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    ChartRing (LiftedUniversalBase.{u} r) i →ₐ[LiftedUniversalBase.{u} r] ChartRing R i := by
  letI := (liftedUniversalSpecialization a).toAlgebra
  exact MvPolynomial.mapAlgHom (Algebra.ofId _ R)

/-- 概要：チャート代入は比座標を保つ。
方針：多項式の係数写像は変数を固定する。
規約：KST Def3.1。使われ方：底変更後の Koszul 微分の同定。 -/
@[simp] theorem liftedUniversalChartSpecialization_coordinate (a : Fin (r + 1) → R)
    (i j : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    liftedUniversalChartSpecializationAlgHom a i (chartCoordinate (LiftedUniversalBase.{u} r) i j) =
      chartCoordinate R i j := by
  let := (liftedUniversalSpecialization a).toAlgebra
  by_cases h : j = i
  · subst j
    simp [chartCoordinate]
  · simp [liftedUniversalChartSpecializationAlgHom, chartCoordinate, h,
      MvPolynomial.mapAlgHom_apply]

/-- 概要：チャート係数環における持ち上げた普遍生成元の像は a_j の定数多項式。
方針：多項式係数の構造射と持ち上げた普遍評価の公式を使う。
規約：KST Def3.1。使われ方：底変更後の関係式の係数の同定。 -/
@[simp] theorem liftedUniversalChartSpecialization_coefficient (a : Fin (r + 1) → R)
    (i j : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    algebraMap (LiftedUniversalBase.{u} r) (ChartRing R i) (liftedUniversalCoefficients r j) =
      MvPolynomial.C (a j) := by
  let := (liftedUniversalSpecialization a).toAlgebra
  change MvPolynomial.C (algebraMap (LiftedUniversalBase.{u} r) R
    (liftedUniversalCoefficients r j)) = MvPolynomial.C (a j)
  congr 1
  exact liftedUniversalSpecialization_generator a j

/-- 概要：持ち上げた普遍チャートの底変更微分は指定係数のチャート微分。
方針：係数族と座標族の特殊化公式を微分の定義へ代入する。
規約：KST Lemma3.6。使われ方：底変更 dg 関手の目標を既存模型へ合わせる。 -/
theorem liftedUniversalChartSpecialization_differential (a : Fin (r + 1) → R)
    (i : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    (chartKoszulDifferential (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i).comp
        LinearMap.id =
      chartKoszulDifferential
        (fun j => algebraMap (LiftedUniversalBase.{u} r) (ChartRing R i)
          (liftedUniversalCoefficients r j))
        (fun j => liftedUniversalChartSpecializationAlgHom a i
          (chartCoordinate (LiftedUniversalBase.{u} r) i j)) i := by
  let := (liftedUniversalSpecialization a).toAlgebra
  simp only [LinearMap.comp_id, liftedUniversalChartSpecialization_coordinate,
    liftedUniversalChartSpecialization_coefficient]

/-- 概要：持ち上げた普遍チャートの dg 底変更を指定係数の標準チャートへ送る。
方針：既存の底変更関手と恒等生成元による微分同定を合成する。
規約：KST Lemma3.6、任意宇宙の可換係数環 R。
使われ方：普遍 dg 解消からの任意基底へのチャート構成。 -/
def liftedUniversalChartBaseChangeDGFunctor (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    EnrichedFunctor (DifferentialGraded.Complex (ChartRing R i))
      (DifferentialGraded.ScalarExtension.DGBaseChange
        (liftedUniversalChartSpecializationAlgHom a i).toRingHom
        (DerivedChartObject (liftedUniversalCoefficients.{u} r) i)) (DerivedChartObject a i) := by
  letI := (liftedUniversalSpecialization a).toAlgebra
  exact EnrichedFunctor.comp (DifferentialGraded.Complex (ChartRing R i))
    (chartBaseChangeDGFunctor (liftedUniversalCoefficients.{u} r) i
      (liftedUniversalChartSpecializationAlgHom a i))
    (exteriorKoszulDGFunctor LinearMap.id _ _ (liftedUniversalChartSpecialization_differential a i))

/-- 概要：任意宇宙での普遍チャート底変更比較は各 Hom 上で可逆。
方針：一般チャート底変更同型と恒等生成元による微分同定を使う。
規約：KST Lemma3.6。使われ方：任意係数チャートとの局所 dg 準同値。 -/
theorem liftedUniversalChartBaseChangeDGFunctor_map_isIso
    (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    ∀ x y, IsIso ((liftedUniversalChartBaseChangeDGFunctor a i).map x y) := by
  let := (liftedUniversalSpecialization a).toAlgebra
  intro x y
  have := chartBaseChangeDGFunctor_map_isIso (liftedUniversalCoefficients.{u} r) i
    (liftedUniversalChartSpecializationAlgHom a i) x y
  change IsIso ((chartBaseChangeDGFunctor (liftedUniversalCoefficients.{u} r) i
      (liftedUniversalChartSpecializationAlgHom a i)).map x y ≫
    (exteriorKoszulCochainIso (LinearEquiv.refl (ChartRing R i) _) _ _
      (liftedUniversalChartSpecialization_differential a i)).hom)
  infer_instance

/-- 概要：任意宇宙の係数環への普遍チャート dg 底変更比較は準同値。
方針：Hom の可逆性と一対象型の本質的全射性を使う。
規約：KST Lemma3.6。使われ方：普遍 Koszul 模型から任意係数のチャートを構成する。 -/
theorem liftedUniversalChartBaseChangeDGFunctor_quasiEquivalence
    (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    letI := (liftedUniversalSpecialization a).toAlgebra
    DifferentialGraded.QuasiEquivalence (liftedUniversalChartBaseChangeDGFunctor a i) := by
  let := (liftedUniversalSpecialization a).toAlgebra
  constructor
  · intro x y
    have := liftedUniversalChartBaseChangeDGFunctor_map_isIso a i x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change DerivedChartObject a i at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
