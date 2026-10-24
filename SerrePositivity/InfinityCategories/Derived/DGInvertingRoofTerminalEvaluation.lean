module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoof
public import SerrePositivity.InfinityCategories.Derived.RoofTerminalEvaluation
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-! # 任意の反転関手の屋根全空間の実評価

概要：任意標的の実屋根全体を固定 Hom へ送り、元の屋根から評価への全実比較を保持する。
方針：左ファイブレーションと恒等分母の終対象性を使い、恒等 fiber の厳密同型で移す。
規約：標的の dg 表示・有限性を仮定しない。使われ方：任意族の屋根評価と全降下作用の比較。
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

/-- 任意標的の実屋根全空間から恒等分母の実 fiber への評価データ。 -/
abbrev DGInvertingRoofTerminalEvaluation (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :=
  RoofTerminalEvaluation (dgInvertingRoofProjection A D P x F z)
    (dgVerdierOverIdentityVertex A D P x)

/-- 任意の反転関手は、屋根全空間上の実評価と実比較を持つ。 -/
theorem dgInvertingRoofTerminalEvaluation_nonempty (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) (z : Y _⦋0⦌) :
    Nonempty (DGInvertingRoofTerminalEvaluation A D P x F z) := by
  have := dgInvertingRoofProjection_leftFibration A D P x F hF z
  exact roofLeftFibration_terminalEvaluation_nonempty
    (dgInvertingRoofProjection A D P x F z) (dgVerdierOverIdentityVertex A D P x)
    (dgVerdierOverIdentityVertex_isTerminal A D P x)

/-- 恒等 fiber の同型で移した、任意標的の固定 Hom への屋根全体の実評価。 -/
def dgInvertingRoofTerminalEvaluationMap (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) :
    dgInvertingRoof A D P x F z ⟶
      pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) z :=
  C.evaluation ≫ (dgInvertingRoofIdentityFiberIso A D P x F z).hom

/-- 元の任意標的屋根から同じ全体評価の固定 Hom 包含への実ホモトピー。 -/
def dgInvertingRoofTerminalEvaluationHomotopy (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) : SSet.Homotopy
    (𝟙 (dgInvertingRoof A D P x F z))
    (dgInvertingRoofTerminalEvaluationMap A D P x F z C ≫
      dgInvertingFixedHomRoofMap A D P x F z) := by
  have he : C.evaluation ≫ vertexFiberι (dgInvertingRoofProjection A D P x F z)
      (dgVerdierOverIdentityVertex A D P x) =
      dgInvertingRoofTerminalEvaluationMap A D P x F z C ≫
        dgInvertingFixedHomRoofMap A D P x F z := by
    dsimp only [dgInvertingRoofTerminalEvaluationMap, dgInvertingFixedHomRoofMap]
    exact roofEvaluationIso_transport _ _ _
  exact stableHomotopyRetarget C.homotopy rfl he

/-- 恒等 fiber の表示への端点輸送は、元の全体比較の全時刻の写像を保持する。 -/
lemma dgInvertingRoofTerminalEvaluationHomotopy_h (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) :
    (dgInvertingRoofTerminalEvaluationHomotopy A D P x F z C).h = C.homotopy.h := rfl

/-- 同じ屋根全体の実評価を、任意の指定パラメータ族へ制限する実ホモトピー。 -/
def dgInvertingRoofTerminalEvaluationFamilyHomotopy (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) {K : SSet.{max u v}}
    (a : K ⟶ dgInvertingRoof A D P x F z) : SSet.Homotopy a
    ((a ≫ dgInvertingRoofTerminalEvaluationMap A D P x F z C) ≫
      dgInvertingFixedHomRoofMap A D P x F z) :=
  stableHomotopyRetarget (functorHomotopyPrecomp
    (dgInvertingRoofTerminalEvaluationHomotopy A D P x F z C) a)
      (Category.comp_id a) (Category.assoc _ _ _).symm

/-- 任意族の評価比較は、全体の同じ実比較写像のパラメータ制限である。 -/
lemma dgInvertingRoofTerminalEvaluationFamilyHomotopy_h (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) {K : SSet.{max u v}}
    (a : K ⟶ dgInvertingRoof A D P x F z) :
    (dgInvertingRoofTerminalEvaluationFamilyHomotopy A D P x F z C a).h =
      (a ▷ (Δ[1] : SSet.{max u v})) ≫ C.homotopy.h := rfl

end SerrePositivity.InfinityCategories
