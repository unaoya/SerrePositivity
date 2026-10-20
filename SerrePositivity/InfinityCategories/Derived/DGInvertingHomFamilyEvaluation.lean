module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofTerminalEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGInvertingHomActionFamily
public import SerrePositivity.InfinityCategories.Derived.DGQuotientHomRoofRepresentation
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentFamilyEvaluation

/-! # 任意族の屋根評価と商 Hom 作用の全選択空間上の比較

概要：任意標的の同じ全体評価を使い、有限商 Hom 図式の実屋根表示と全作用族を比較する。
方針：実屋根比較ホモトピーと全体評価の実ホモトピーを、全パラメータ降下比較へ代入する。
規約：全体評価は全パラメータ族で共有できる。使われ方：任意標的の合成評価族との接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 指定実屋根族と商 Hom 族の実比較から、全降下選択空間上の同じ評価比較を得る。 -/
def dgInvertingHomActionFamilyEvaluationIso (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (C : DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))) {K : SSet.{max u v}}
    (a : K ⟶ dgRoofCorrespondence A D P x y)
    (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
    (HQ : SSet.Homotopy (a ≫ dgRoofCorrespondenceMap A D P x y)
      (b ≫ dgQuotientFixedHomRoofMap A D P x y)) :
    FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
      (SSet.const (functorVertex (a ≫ dgInvertingRoofFunctorMap A D P x y F ≫
        dgInvertingRoofTerminalEvaluationMap A D P x F
          (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) C))) :=
  weakRoofDescentActionFamilyEvaluationIso (dgRoofCorrespondenceMap A D P x y)
    (dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F) (dgQuotientFixedHomRoofMap A D P x y) a b
    (a ≫ dgInvertingRoofFunctorMap A D P x y F ≫ dgInvertingRoofTerminalEvaluationMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) C) HQ
    (dgInvertingRoofTerminalEvaluationFamilyHomotopy A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) C (a ≫ dgInvertingRoofFunctorMap A D P x y F))

/-- 指定商 Hom 族の実屋根表示と、同じ全体評価を用いた全降下選択空間上の関手同型。 -/
structure DGInvertingHomFamilyEvaluation (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (C : DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))) {K : SSet.{max u v}}
    (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) where
  roofFamily : K ⟶ dgRoofCorrespondence A D P x y
  comparison : SSet.Homotopy (roofFamily ≫ dgRoofCorrespondenceMap A D P x y)
    (b ≫ dgQuotientFixedHomRoofMap A D P x y)
  evaluationIso : FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
    (SSet.const (functorVertex (roofFamily ≫ dgInvertingRoofFunctorMap A D P x y F ≫
      dgInvertingRoofTerminalEvaluationMap A D P x F
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) C)))

/-- 同じ全体評価を固定したまま、任意の有限商 Hom 図式を全選択空間上で実評価と比較する。 -/
theorem dgInvertingHomFamilyEvaluation_nonempty (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (C : DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))) {K : SSet.{max u v}} [K.Finite]
    (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) :
    Nonempty (DGInvertingHomFamilyEvaluation A D P x y F C b) := by
  obtain ⟨a, ⟨HQ⟩⟩ := dgQuotientHomFinite_actualRoofLift A D P hP x y b
  exact ⟨⟨a, HQ, dgInvertingHomActionFamilyEvaluationIso A D P x y F C a b HQ⟩⟩

/-- 任意の反転関手と有限商 Hom 図式は、共有可能な全体評価と全パラメータ実比較を持つ。 -/
theorem dgInvertingHomFamilyEvaluation_exists (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) {K : SSet.{max u v}} [K.Finite]
    (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) :
    ∃ C : DGInvertingRoofTerminalEvaluation A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)),
      Nonempty (DGInvertingHomFamilyEvaluation A D P x y F C b) := by
  obtain ⟨C⟩ := dgInvertingRoofTerminalEvaluation_nonempty A D P x F hF
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  exact ⟨C, dgInvertingHomFamilyEvaluation_nonempty A D P hP x y F C b⟩

end SerrePositivity.InfinityCategories
