module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessEdges

/-!
概要：任意の可換四角形が transport representation となる条件。
方針：四角形の比較を fiber へ制限し、普遍 pointed-space fiber への射で同値性を検査する。
規約：表現の条件を先に仮定せず、実際の四角形に対して判定する。
使われ方：Kerodon §5.6.8（Tag 02S9）、可逆な辺に沿う表現条件の不変性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：可換四角形から分類図式の unstraightening への底上の比較を作る。
方針：四角形の二つの射を引き戻しへ持ち上げる。
規約：fiber の同値性を要求しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現条件の検査対象となる実際の比較。 -/
noncomputable def LeftTransportSquare.comparison {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening S.diagram :=
  pullback.lift S.pointedMap p S.comm

/-- 概要：四角形から作った比較は底を厳密に保つ。
方針：引き戻しへの持ち上げの第二射影を計算する。
規約：元の射影 p の充填性は不要。
使われ方：Kerodon §5.6.8（Tag 02S9）、比較の fiber への制限。 -/
lemma LeftTransportSquare.comparison_projection {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) : S.comparison ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection S.diagram = p :=
  pullback.lift_snd _ _ _

/-- 概要：可換四角形の各 fiber から普遍 pointed-space fiber への比較。
方針：底上の比較の fiber 射に標準 fiber 同型を合成する。
規約：四角形が表現であるという条件は不要。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現条件の可逆な辺に沿う移送。 -/
noncomputable def LeftTransportSquare.pointedFiberMap {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (S.diagram.app _ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection S.diagram) S.comparison
    S.comparison_projection b ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso S.diagram b).hom

/-- 概要：四角形の fiber 比較の包含は pointed space への射の制限。
方針：標準 fiber 同型と比較射の包含公式を使う。
規約：厳密な射の等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、fiber 上の比較 prism の端点条件。 -/
lemma LeftTransportSquare.pointedFiberMap_ι {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (b : B _⦋0⦌) :
    S.pointedFiberMap b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (S.diagram.app _ b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ S.pointedMap := by
  rw [LeftTransportSquare.pointedFiberMap, Category.assoc]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection S.diagram b).hom ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection S.diagram) S.comparison
    S.comparison_projection b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection S.diagram) b) ≫
      pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection S.diagram = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.assoc]
  exact congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ f) (pullback.lift_fst _ _ _)

/-- 概要：四角形が表現となる fiber 条件。
方針：全ての普遍 fiber への比較の同値性を要求する。
規約：p は left fibration で、元の底の quasicategory 性は要求しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、全部分複体の頂点条件の具体的な判定。 -/
def LeftTransportSquare.IsRepresentation {E B : SSet.{u + 1}} {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) : Prop := ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (S.pointedFiberMap b)

/-- 概要：fiber 条件を満たす四角形を実際の表現に束ねる。
方針：普遍 fiber の同型を二対三則で消去する。
規約：元の四角形の両射を使う。
使われ方：Kerodon §5.6.8（Tag 02S9）、延長した四角形の終点を表現へ戻す。 -/
noncomputable def LeftTransportSquare.toRepresentation {E B : SSet.{u + 1}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (hS : S.IsRepresentation) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p where
  diagram := S.diagram
  comparison := S.comparison
  over_base := S.comparison_projection
  fiber_equivalence b :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso S.diagram b)).isQCatEquivalence.cancel_right
      (hS b)

/-- 概要：四角形から作った表現は元の四角形を厳密に回収する。
方針：底側は定義、全空間側は引き戻しの第一射影で比較する。
規約：表現の存在命題ではなくデータの等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、延長した終点の頂点条件の確認。 -/
lemma LeftTransportSquare.toRepresentation_toSquare {E B : SSet.{u + 1}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p) (hS : S.IsRepresentation) :
    (S.toRepresentation hS).toSquare = S := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.ext
  · rfl
  · exact pullback.lift_fst _ _ _

/-- 概要：表現から得た四角形の fiber 比較は元の表現の比較と同じ。
方針：普遍 fiber の包含後に同じ pointed space への射になることを使う。
規約：射そのものの等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、頂点条件と fiber 条件の同値。 -/
lemma LeftTransportRepresentation.toSquare_pointedFiberMap {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (b : B _⦋0⦌) :
    R.toSquare.pointedFiberMap b = R.pointedFiberMap b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (R.diagram.app _ b)
  exact (R.toSquare.pointedFiberMap_ι b).trans (R.pointedFiberMap_ι b).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (toSquare_pointedFiberMap)


/-- 概要：実際の表現から得た四角形は fiber 条件を満たす。
方針：元の表現の普遍 fiber 比較の同値性を使う。
規約：同じ表現の両射を保持する。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現条件の移送の初期値。 -/
lemma LeftTransportRepresentation.toSquare_isRepresentation {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) :
    R.toSquare.IsRepresentation := by
  intro b
  rw [R.toSquare_pointedFiberMap]
  exact R.pointedFiberMap_isQCatEquivalence b

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (toSquare_isRepresentation)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
