module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の単体集合上の空間値 covariant transport representation のデータ。
方針：分類図式と unstraightening への底上の比較を束ね、全 fiber の同値性を要求する。
規約：表現の存在や境界付き延長を構造の仮定として隠さない。
使われ方：Kerodon §§5.6.2（Tag 026H）、5.6.5（Tag 028U）、底と全空間の比較を同時に固定する相対延長。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

local instance representationPullbackLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：全空間の底上の同型は各頂点の fiber の同型を与える。
方針：同型の両方向を fiber に制限し、合成則で往復を確認する。
規約：fibration 性や基底の quasicategory 性は不要。
使われ方：Kerodon §5.6.2（Tag 026H）、表現の底変換の同型を fiber の比較へ移す。 -/
def vertexFiberIsoOfTotalIso {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (e : E ≅ E') (he : e.hom ≫ q = p) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q e.hom he b
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p e.inv (by rw [← he, Iso.inv_hom_id_assoc]) b
  hom_inv_id := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_comp]
    simp only [Iso.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id]
  inv_hom_id := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_comp]
    simp only [Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id]

/-- 概要：底上の比較の全 fiber の同値性は任意の底変換で保たれる。
方針：引き戻しの fiber 同型で元の比較に戻す。
規約：比較する二つの射影は left fibrations。底の quasicategory 性は不要。
使われ方：Kerodon §5.6.5（Tag 028U）、境界やパラメーターへの表現の制限。 -/
lemma fiberComparisonBaseChange_isQCatEquivalence_fibers
    {E E' B D : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b))
    (g : D ⟶ B) (d : D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.snd p g) (pullback.snd q g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf g) d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso q g d)).isQCatEquivalence.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.snd p g) (pullback.snd q g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf g) d ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso q g d).hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_fiber]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p g d)).isQCatEquivalence.comp (h _)

/-- 概要：空間値の図式が p を表現するデータを束ねる。
方針：unstraightening への底上の比較に各 fiber の同値性を添える。
規約：比較射は実際の単体集合の射であり、同値類や存在命題ではない。
使われ方：Kerodon Theorem 5.6.5.12（Tag 0293）、境界上で指定する表現の入力。 -/
@[kerodon 05QT]
structure LeftTransportRepresentation {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] where
  diagram : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  comparison : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening diagram
  over_base : comparison ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection diagram = p
  fiber_equivalence : ∀ b : B _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection diagram)
      comparison over_base b)

/-- 概要：表現の全空間の射を pointed space への射として回収する。
方針：unstraightening の第一射影へ合成する。
規約：表現の比較射そのものから作る。
使われ方：Kerodon §5.6.5（Tag 028U）、底の射と同時に固定する全空間側のデータ。 -/
noncomputable def LeftTransportRepresentation.pointedMap {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : LeftTransportRepresentation p) :
    E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  R.comparison ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection R.diagram

/-- 概要：表現の pointed space への射と分類図式は厳密な可換四角形をなす。
方針：引き戻し条件と底上の比較の可換性を合成する。
規約：ホモトピー可換に弱めない。
使われ方：Kerodon Theorem 5.6.5.12（Tag 0293）、境界上で固定する四角形。 -/
lemma LeftTransportRepresentation.pointedMap_projection {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : LeftTransportRepresentation p) :
    R.pointedMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = p ≫ R.diagram := by
  rw [LeftTransportRepresentation.pointedMap, Category.assoc, pullback.condition,
    ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ R.diagram) R.over_base

/-- 概要：表現の比較射は pointed space の射と底の射から厳密に回収できる。
方針：引き戻しの二射影で比較する。
規約：境界上で固定すべきデータの二つの記述を同一視する。
使われ方：Kerodon §5.6.5（Tag 028U）、全空間の射を保つ相対延長の定式化。 -/
lemma LeftTransportRepresentation.comparison_eq_lift {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : LeftTransportRepresentation p) :
    R.comparison = pullback.lift R.pointedMap p R.pointedMap_projection := by
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
    rfl
  · change R.comparison ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection R.diagram = _
    simpa only [pullback.lift_snd] using R.over_base

/-- 概要：left fibration の表現の比較は全空間の前合成同値。
方針：任意の底上の left fibrations の fiber 判定を使う。
規約：底の quasicategory 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、表現から実際の全空間比較を得る。 -/
lemma LeftTransportRepresentation.isPrecompositionEquivalence {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : LeftTransportRepresentation p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence R.comparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isPrecompositionEquivalence_of_leftFibration_fibers p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection R.diagram) R.comparison R.over_base R.fiber_equivalence

/-- 概要：unstraightening の標準射影は元の分類図式による標準表現を持つ。
方針：比較に恒等射を取り、fiber の恒等射を同値とする。
規約：任意の底の coherent な図式に適用する。
使われ方：Kerodon §5.6.2（Tag 026H）、相対表現の標準例。 -/
noncomputable def unstraighteningTransportRepresentation {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    LeftTransportRepresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) where
  diagram := F
  comparison := 𝟙 _
  over_base := Category.id_comp _
  fiber_equivalence b := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence

/-- 概要：表現は分類図式と pointed space への全空間の射で一意に決まる。
方針：底側を同定し、全空間の比較を引き戻しの二射影で比較する。
規約：表現のデータの厳密な等式。
使われ方：Kerodon Theorem 5.6.5.12（Tag 0293）、両側の射を固定する延長条件の判定。 -/
lemma LeftTransportRepresentation.ext {E B : SSet.{u + 1}} {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R S : LeftTransportRepresentation p) (hF : R.diagram = S.diagram)
    (hpointed : R.pointedMap = S.pointedMap) : R = S := by
  cases R with
  | mk F f hf ef =>
    cases S with
    | mk G g hg eg =>
      dsimp only at hF
      cases hF
      have hfg : f = g := by
        apply pullback.hom_ext
        · exact hpointed
        · exact hf.trans hg.symm
      cases hfg
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
