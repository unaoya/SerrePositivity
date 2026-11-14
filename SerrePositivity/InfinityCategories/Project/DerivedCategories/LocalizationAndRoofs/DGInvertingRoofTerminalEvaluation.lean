module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGInvertingRoof
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofTerminalEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 任意標的の実屋根全空間から恒等分母の実 fiber への評価データ。 -/
abbrev DGInvertingRoofTerminalEvaluation (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (z : Y _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)

/-- 任意の反転関手は、屋根全空間上の実評価と実比較を持つ。 -/
theorem dgInvertingRoofTerminalEvaluation_nonempty (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) (z : Y _⦋0⦌) :
    Nonempty (DGInvertingRoofTerminalEvaluation A D P x F z) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection_leftFibration A D P x F hF z
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofLeftFibration_terminalEvaluation_nonempty
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F z) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex_isTerminal A D P x)

/-- 恒等 fiber の同型で移した、任意標的の固定 Hom への屋根全体の実評価。 -/
def dgInvertingRoofTerminalEvaluationMap (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F z ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) z :=
  C.evaluation ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofIdentityFiberIso A D P x F z).hom

/-- 元の任意標的屋根から同じ全体評価の固定 Hom 包含への実ホモトピー。 -/
def dgInvertingRoofTerminalEvaluationHomotopy (P : Set D) (x : D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) : SSet.Homotopy
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F z))
    (dgInvertingRoofTerminalEvaluationMap A D P x F z C ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F z) := by
  have he : C.evaluation ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) =
      dgInvertingRoofTerminalEvaluationMap A D P x F z C ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F z := by
    dsimp only [dgInvertingRoofTerminalEvaluationMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationIso_transport _ _ _
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget C.homotopy rfl he

/-- 恒等 fiber の表示への端点輸送は、元の全体比較の全時刻の写像を保持する。 -/
lemma dgInvertingRoofTerminalEvaluationHomotopy_h (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) :
    (dgInvertingRoofTerminalEvaluationHomotopy A D P x F z C).h = C.homotopy.h := rfl

/-- 同じ屋根全体の実評価を、任意の指定パラメータ族へ制限する実ホモトピー。 -/
def dgInvertingRoofTerminalEvaluationFamilyHomotopy (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) {K : SSet.{max u v}}
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F z) : SSet.Homotopy a
    ((a ≫ dgInvertingRoofTerminalEvaluationMap A D P x F z C) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F z) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (dgInvertingRoofTerminalEvaluationHomotopy A D P x F z C) a)
      (Category.comp_id a) (Category.assoc _ _ _).symm

/-- 任意族の評価比較は、全体の同じ実比較写像のパラメータ制限である。 -/
lemma dgInvertingRoofTerminalEvaluationFamilyHomotopy_h (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (z : Y _⦋0⦌)
    (C : DGInvertingRoofTerminalEvaluation A D P x F z) {K : SSet.{max u v}}
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F z) :
    (dgInvertingRoofTerminalEvaluationFamilyHomotopy A D P x F z C a).h =
      (a ▷ (Δ[1] : SSet.{max u v})) ≫ C.homotopy.h := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
