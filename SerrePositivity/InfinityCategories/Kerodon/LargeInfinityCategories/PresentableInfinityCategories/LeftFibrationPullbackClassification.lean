module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationPullbackLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FlipEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyReadback

/-!
概要：left fibrations の引き戻しを分類し、全パラメーターの空間値極限錐族を構成する。
方針：全豊穣 Hom による極限錐を同じ straightening 同値で送り、二変数を交換する。
規約：値ごとの同値族から自然性を推測せず、一つの全空間の錐を使う。
使われ方：引き戻し内の共変 Hom の filtered 余極限保存。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


variable {E D B X : SSet.{u}} [Quasicategory X]
  (p : E ⟶ B) (q : D ⟶ B) (e : E ⟶ X) (d : D ⟶ X) (b : B ⟶ X)
  (hp : p ≫ b = e) (hq : q ≫ b = d)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration b] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]

/-- 概要：元の全空間の引き戻しを分類した関手圏内の全錐。
方針：構成した coherent な全錐へ同じ straightening を合成する。
規約：分類関手を選び直さない。
使われ方：空間値の全極限錐族の構成。 -/
def leftFibrationPullbackClassifiedCone :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPullbackOrdinaryCone p q e d b hp hq))

/-- 概要：分類した引き戻し錐は関手圏内の極限錐。
方針：元の全空間の錐の極限性を同じ分類同値で送る。
規約：一般の局所化存在定理を使わない。
使われ方：各点での全極限性への移送。 -/
lemma leftFibrationPullbackClassifiedCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (leftFibrationPullbackClassifiedCone p q e d b hp hq) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence X).isLimitCone_iff _ |>.mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPullbackCone_isLimit p q e d b hp hq)

/-- 概要：分類した引き戻し錐は各点で空間の極限錐。
方針：小さい cospan 上の空間の極限の存在と全錐の普遍性を使う。
規約：元の全錐の各点計算を主張する。
使われ方：転置した全極限錐族の普遍性。 -/
lemma leftFibrationPullbackClassifiedCone_isPointwiseLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseLimitCone (leftFibrationPullbackClassifiedCone p q e d b hp hq) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits
    (fun _ ↦ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.space_hasSmallLimits _ _) _
  exact leftFibrationPullbackClassifiedCone_isLimit p q e d b hp hq

/-- 概要：元の底全体をパラメーターとする空間の全極限錐族。
方針：同じ分類済み全錐の二変数を交換する。
規約：全高次パラメーターを保持する。
使われ方：filtered 余極限と cospan 極限の交換。 -/
def leftFibrationPullbackLimitFamily :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _ (leftFibrationPullbackClassifiedCone p q e d b hp hq).val

/-- 概要：全族の各点は元の分類錐を評価した極限錐。
方針：二変数交換の零単体公式と元の全錐の各点計算を使う。
規約：全族の図式・頂点の双方を固定する。
使われ方：元の引き戻し Hom 全族への形状交換の適用。 -/
lemma leftFibrationPullbackLimitFamily_isLimit
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone
      ((leftFibrationPullbackLimitFamily p q e d b hp hq).app (Opposite.op ⦋0⦌) x)) := by
  rw [leftFibrationPullbackLimitFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_functorVertexCone_functorVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone (leftFibrationPullbackClassifiedCone p q e d b hp hq) x)).mpr
      (leftFibrationPullbackClassifiedCone_isPointwiseLimit p q e d b hp hq x)

omit [Quasicategory X] in
/-- 概要：全極限錐族の頂点評価は元の引き戻し射影の分類図式そのもの。
方針：転置の頂点公式と strict な錐の頂点回収を使う。
規約：関手の全自然な等式であり、値ごとの同型に弱めない。
使われ方：元の共変 Hom 関手の保存性を全錐の交換から回収する。 -/
lemma leftFibrationPullbackLimitFamily_apex :
    leftFibrationPullbackLimitFamily p q e d b hp hq ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) _)) =
      @_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram _ _ (pullback.fst p q ≫ e)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativePullbackProjection_leftFibration p q e d b hp hq) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativePullbackProjection_leftFibration p q e d b hp hq
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [leftFibrationPullbackLimitFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.flipFamily_evaluate_vertex]
  change (leftFibrationPullbackClassifiedCone p q e d b hp hq).vertex = _
  rw [leftFibrationPullbackClassifiedCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_vertex (pullback.fst p q ≫ e)).symm

omit [Quasicategory X] in
/-- 概要：全錐族の各脚の評価は元の指定 fibration の分類写像の値。
方針：二変数交換の全評価公式と元の strict 図式の対象公式を合わせる。
規約：対象の同値類でなく関手頂点の厳密な等式。
使われ方：成分の共変 Hom 全族への読み戻し。 -/
lemma leftFibrationPullbackLimitFamily_right_vertex (k : AsSmall.{u} WalkingCospan) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (leftFibrationPullbackLimitFamily p q e d b hp hq ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))).app
          (Opposite.op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ k)))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap X).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPullbackDiagram p q e d b hp hq).obj k)) := by
  rw [leftFibrationPullbackLimitFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.flipFamily_evaluate_vertex]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (leftFibrationPullbackClassifiedCone p q e d b hp hq).val).app
    (Opposite.op ⦋0⦌)
    (ULift.up (ComposableArrows.mk₀ k))) = _
  rw [(leftFibrationPullbackClassifiedCone p q e d b hp hq).property]
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact congrArg
    (fun v : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X)) _⦋0⦌ ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap X).app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPullbackDiagram p q e d b hp hq) k)

omit [Quasicategory X] in
/-- 概要：全錐族の左脚評価は元の第一射影の分類図式。
方針：元の cospan の左対象の厳密な頂点公式を使う。
規約：元の全分類関手の等式。
使われ方：第一成分の filtered 余極限保存への読み戻し。 -/
lemma leftFibrationPullbackLimitFamily_left :
    leftFibrationPullbackLimitFamily p q e d b hp hq ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))).app _
          (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [leftFibrationPullbackLimitFamily_right_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_vertex e).symm

omit [Quasicategory X] in
/-- 概要：全錐族の右脚評価は元の第二射影の分類図式。
方針：元の cospan の右対象の厳密な頂点公式を使う。
規約：元の全分類関手の等式。
使われ方：第二成分の filtered 余極限保存への読み戻し。 -/
lemma leftFibrationPullbackLimitFamily_right :
    leftFibrationPullbackLimitFamily p q e d b hp hq ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))).app _
          (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram d := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [leftFibrationPullbackLimitFamily_right_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_vertex d).symm

omit [Quasicategory X] in
/-- 概要：全錐族の底の評価は元の共通標的の分類図式。
方針：元の cospan の終対象の厳密な頂点公式を使う。
規約：元の全分類関手の等式。
使われ方：標的像の filtered 余極限保存への読み戻し。 -/
lemma leftFibrationPullbackLimitFamily_base :
    leftFibrationPullbackLimitFamily p q e d b hp hq ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))).app _
          (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.one)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [leftFibrationPullbackLimitFamily_right_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_vertex b).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
