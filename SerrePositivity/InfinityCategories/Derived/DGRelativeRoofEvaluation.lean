module
public import SerrePositivity.InfinityCategories.Derived.RoofRelativeEvaluationIso
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofImageProjections
public import SerrePositivity.InfinityCategories.Derived.DGClosedDenominatorHomotopy
/-!
概要：任意反転標的の実屋根を、指定部分の値・全比較・指定実分母の全底を保って評価する。
方針：実屋根射影の left fibration 性と、恒等分母 fiber の同型を相対評価に適用する。
規約：有限性を仮定しない。使われ方：全高次境界を保つ評価の同時選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {L K Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
variable (r : DGClosedVerdierDenominators A D P x)
variable (n : K ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) r.obj.left) y)
variable (i : L ⟶ K)
variable (g : L ⟶ pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
  (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
variable (H : SSet.Homotopy
  (i ≫ ((n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ dgInvertingRoofFunctorMap A D P x y F))
  (g ≫ dgInvertingFixedHomRoofMap A D P x F
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))))
/-- 指定部分の値と全比較を保つ、指定実分母上の任意標的への実屋根評価。 -/
structure DGRelativeRoofEvaluation where
  value : K ⟶ pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  value_boundary : i ≫ value = g
  homotopy : SSet.Homotopy
    ((n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ dgInvertingRoofFunctorMap A D P x y F)
    (value ≫ dgInvertingFixedHomRoofMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
  projection : homotopy.h ≫ dgInvertingRoofProjection A D P x F
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) =
      (dgClosedDenominatorHomotopy A D P x r K).h
  boundary : (i ▷ (Δ[1] : SSet.{max u v})) ≫ homotopy.h = H.h
/-- 任意の指定部分の値と実比較を全時刻で固定し、同じ実分母の底上で評価を延長する。 -/
lemma dgRelativeRoofEvaluation_nonempty [Quasicategory Y] [Mono i]
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (hH : H.h ≫ dgInvertingRoofProjection A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) =
        (i ▷ (Δ[1] : SSet.{max u v})) ≫ (dgClosedDenominatorHomotopy A D P x r K).h) :
    Nonempty (DGRelativeRoofEvaluation A D P x y F r n i g H) := by
  let p := dgInvertingRoofProjection A D P x F
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  have : LeftFibration p := dgInvertingRoofProjection_leftFibration A D P x F hF _
  let a := (n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ dgInvertingRoofFunctorMap A D P x y F
  have ha : a ≫ p = SSet.const (dgClosedVerdierDenominatorVertex A D P x r) := by
    dsimp only [a, p]
    rw [Category.assoc, dgInvertingRoofFunctorMap_projection, Category.assoc,
      dgClosedRoofHomInclusion_projection, SSet.comp_const]
  let β := stableHomotopyRetarget (dgClosedDenominatorHomotopy A D P x r K) ha.symm rfl
  obtain ⟨R⟩ := roofRelativeIsoEvaluation_nonempty p (dgVerdierOverIdentityVertex A D P x)
    (dgInvertingRoofIdentityFiberIso A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))) i a g H β hH
  exact ⟨⟨R.value, R.value_boundary, R.homotopy, R.over, R.boundary⟩⟩
end SerrePositivity.InfinityCategories
