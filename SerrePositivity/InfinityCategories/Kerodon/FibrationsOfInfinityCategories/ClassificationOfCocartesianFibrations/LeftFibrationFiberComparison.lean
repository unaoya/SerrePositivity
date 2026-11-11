module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.F1BKanExtensionLeftFibrationNerveComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrecompositionSimplexLocality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSourceIso

/-!
概要：任意の底上の left fibrations の射を fiber ごとに比較する判定。
方針：底の各標準単体を有限鎖の nerve へ移し、底変換した比較に scaffold の定理を使う。
規約：底の quasicategory 性は前合成同値の結論には不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent 図式の復元候補を全空間で比較する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (b : B _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration p b

/-- 概要：底を保つ比較射の各 fiber の同値性は、nerve を定義域とする底変換でも全空間の同値を与える。
方針：引き戻しの fiber 同型で元の fiber の同値へ戻し、通常の nerve 上の判定を適用する。
規約：底の圏の対象ごとの fiber の比較を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、各標準単体上での比較。 -/
lemma kanIsPrecompositionEquivalence_leftFibration_nerveBaseChange
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b))
    {C : Type u} [Category.{u} C] (g : nerve C ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd q g) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd q g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q))⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.F1BKanExtensionLeftFibrationNerveComparison.kanIsPrecompositionEquivalence_of_leftFibration_nerve_fibers
    (pullback.snd p g) (pullback.snd q g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf g)
  intro c
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso q g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).isQCatEquivalence.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.snd p g) (pullback.snd q g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso q g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_fiber]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).isQCatEquivalence.comp (h _)

/-- 概要：任意の底上の left fibrations の射は各 fiber で同値なら前合成同値。
方針：各標準単体を有限鎖の nerve と同定し、底変換の比較と全空間の局所性を使う。
規約：元の底 B は quasicategory でなくてもよい。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の全空間での比較。 -/
lemma kanIsPrecompositionEquivalence_of_leftFibration_fibers
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  let u : Over.mk p ⟶ Over.mk q := Over.homMk f hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_of_pullback_stdSimplex u
  intro n s
  let g : nerve (ULift.{u} (Fin (n + 1))) ⟶ B := (stdSimplex.isoNerve n).inv ≫ s
  have hb := kanIsPrecompositionEquivalence_leftFibration_nerveBaseChange p q f hf h g
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (pullbackSymmetry g p)).comp hb
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_overPullbackMap] at hc
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (pullbackSymmetry g q)).cancel_right hc
  let e : Over.mk s ≅ Over.mk g := Over.isoMk (stdSimplex.isoNerve n) (by
    change (stdSimplex.isoNerve n).hom ≫ g = s
    exact Iso.hom_inv_id_assoc _ _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat u) e hd

/-- 概要：left fibrations の底上の射は各 fiber で同値なら全空間の quasicategory の同値。
方針：fiber ごとの前合成同値の判定を適用し、quasicategory 間の同値を回収する。
規約：全空間の quasicategory 性は、底が quasicategory の場合は射影から従う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元比較射の同値判定。 -/
lemma kanIsQCatEquivalence_of_leftFibration_fibers
    {E E' B : SSet.{u}} [Quasicategory E] [Quasicategory E']
    (p : E ⟶ B) (q : E' ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f :=
  (kanIsPrecompositionEquivalence_of_leftFibration_fibers p q f hf h).isQCatEquivalence

/-- 概要：各 fiber で同値な left fibrations の比較は任意の底変換後も前合成同値。
方針：引き戻しの fiber の同型で元の条件へ戻し、全空間の fiber 判定を適用する。
規約：元の底と底変換の始域の quasicategory 性は不要。
使われ方：局所 Kan 添字の区間模型への比較を関手に沿って引き戻す。 -/
lemma kanIsPrecompositionEquivalence_leftFibration_baseChange
    {E E' B A : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) (g : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd q g) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd q g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q))⟩
  apply kanIsPrecompositionEquivalence_of_leftFibration_fibers
    (pullback.snd p g) (pullback.snd q g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf g)
  intro a
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso q g a)).isQCatEquivalence.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.snd p g) (pullback.snd q g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange p q f hf g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection p q f hf g) a ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso q g a).hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1BFibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_fiber]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p g a)).isQCatEquivalence.comp
    (h _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
