module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTrivialComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-!
概要：単射な前合成同値による left fibration の相対内部 Hom の比較。
方針：内部 Hom の二つの前合成の全境界持ち上げ性から相対比較の同値性を得て、left fibration の判定を使う。
規約：底は quasicategory。モデル構造の弱同値は使わない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対関手空間と分類の写像空間の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単射な前合成同値と left fibration の相対内部 Hom の比較は trivial Kan fibration。
方針：底の前合成の引き戻しを消去して全空間の前合成の同値へ戻し、left fibration の同値判定を使う。
規約：p の底 B は quasicategory、始域の単体集合には充填性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、固定した底上の図式の厳密な延長。 -/
lemma trivialKanFibration_relativeHom_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (i : D ⟶ A) [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (r : internalHom.PullbackObjObj i p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration r.π := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : Quasicategory ((internalHom.obj (Opposite.op A)).obj E) :=
    inferInstanceAs (Quasicategory ((ihom A).obj E))
  have : Quasicategory ((internalHom.obj (Opposite.op D)).obj E) :=
    inferInstanceAs (Quasicategory ((ihom D).obj E))
  have := hi.trivialKanFibration_pre B
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration r.fst :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback r.isPullback.flip
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := (pre i).app B))⟩
  have : Quasicategory r.pt := quasicategory_of_innerFibration r.fst
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r.π := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ i p r
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence r.π := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration r.fst).cancel_right
    rw [r.π_fst]
    exact hi E
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trivialKanFibration_of_leftFibration_of_isQCatEquivalence r.π he

/-- 概要：単射な前合成同値による相対関手空間の制限は trivial Kan fibration。
方針：相対内部 Hom の全境界持ち上げを固定した底の図式の fiber へ制限する。
規約：元の p は quasicategory の底を持つ left fibration。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対関手の比較の存在と高次の一意性。 -/
lemma relativeFunctorPre_trivialKanFibration_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a : A ⟶ B) (i : D ⟶ A) [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) := by
  let r := Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := trivialKanFibration_relativeHom_of_precompositionEquivalence i hi p r
  constructor
  intro T U j hj
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := r.π) j hj
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.hasLiftingProperty_relativeFunctorPre p a i r j

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
