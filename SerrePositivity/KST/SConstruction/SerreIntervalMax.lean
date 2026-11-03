module
public import SerrePositivity.KST.SConstruction.SerreIntervalContraction
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-! # 元の鎖区間の max connection
概要：一端点への収縮を転置して、元の鎖区間の max connection の chain map を作る。
方針：零端点を恒等射、辺を収縮へ写す Hom 値の lift を逆転置する。
規約：元の端点と辺を保持する。使われ方：cubical connection と Serre 対角の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 零端点を恒等射、元の辺を一端点への収縮に写す Hom 値の chain map。 -/
def serreIntervalMaxCurried : serreInterval A ⟶ homComplex A (serreInterval A) (serreInterval A) :=
  serreIntervalLift A (identity (serreInterval A)) (serreIntervalContraction A)

/-- max connection の元の二変数 chain map。 -/
def serreIntervalMax : serreInterval A ⊗ serreInterval A ⟶ serreInterval A :=
  uncurryRight (serreIntervalMaxCurried A)

/-- 元の零端点は、転置前の恒等射を回収する。 -/
lemma serreIntervalMaxCurried_zero :
    serreIntervalZero A ≫ serreIntervalMaxCurried A = identity (serreInterval A) :=
  serreIntervalLift_zero A _ _

/-- 元の辺は、同じ一端点への収縮を回収する。 -/
lemma serreIntervalMaxCurried_edge :
    (serreIntervalMaxCurried A).f (-1) (serreIntervalEdge A) = serreIntervalContraction A :=
  serreIntervalLift_edge A _ _

/-- 元の一端点は、転置前の一端点への同じ定数射を回収する。 -/
lemma serreIntervalMaxCurried_one :
    serreIntervalOne A ≫ serreIntervalMaxCurried A =
      closedMap A (serreIntervalAugmentation A ≫ serreIntervalOne A) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (serreIntervalOne A ≫
    serreIntervalLift A (identity (serreInterval A)) (serreIntervalContraction A))).val =
      (cycleFromUnit _ (closedMap A (serreIntervalAugmentation A ≫ serreIntervalOne A))).val
  rw [serreIntervalLift_one_cycle]
  simp only [identity, cycleFromUnit_unitFromCycle, closedMap_cycle]
  change Cochain.ofHom (𝟙 (serreInterval A)) + δ (-1) 0 (serreIntervalContraction A) = _
  rw [serreIntervalContraction_d]
  abel

/-- max connection の元の零左端点への制限は、元の左単位射。 -/
lemma serreIntervalMax_zero_left :
    serreIntervalZero A ▷ serreInterval A ≫ serreIntervalMax A = (λ_ (serreInterval A)).hom := by
  rw [serreIntervalMax, ← uncurryRight_precompose, serreIntervalMaxCurried_zero,
    uncurryRight_identity]

/-- max connection の元の一左端点への制限は、同じ一端点への定数射。 -/
lemma serreIntervalMax_one_left :
    serreIntervalOne A ▷ serreInterval A ≫ serreIntervalMax A =
      (λ_ (serreInterval A)).hom ≫ serreIntervalAugmentation A ≫ serreIntervalOne A := by
  rw [serreIntervalMax, ← uncurryRight_precompose, serreIntervalMaxCurried_one,
    uncurryRight_closedMap]

/-- max connection の全斉次成分は、元の Hom 値の射による評価。 -/
lemma serreIntervalMax_apply (p q n : ℤ) (hn : p + q = n)
    (x : (serreInterval A).X p) (y : (serreInterval A).X q) :
    (serreIntervalMax A).f n (ιTensorObj (serreInterval A) (serreInterval A) p q n hn
        (x ⊗ₜ[A] y)) = ((serreIntervalMaxCurried A).f p x).v q n (by omega) y :=
  uncurryRight_apply _ p q n hn x y

end SerrePositivity.KST.SConstruction
