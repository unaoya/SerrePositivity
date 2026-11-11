module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareComparisonVertical
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceConverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTrivialComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite

/-!
概要：合成射と後半の射の相対 coslice の充填性から前半の充填性を導く。
方針：縦比較の後半を底変換し、同値の消去則と left fibration の判定を使う。
規約：三つの全空間は quasicategory、前半の射は inner fibration。
使われ方：合成射に関する cocartesian 性を中間の射に移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：合成と後半の相対 coslice が自明なら前半も自明 Kan fibration。
方針：縦合成の比較の因子分解に同値の右消去を適用する。
規約：図式とその部分複体は任意。
使われ方：射影の合成に関する cocartesian 辺の消去。 -/
lemma kanRelativeCosliceMap_trivialKanFibration_cancel {K X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (e : K ⟶ X) (p : X ⟶ Y) (q : Y ⟶ Z) [InnerFibration p]
    (K₀ : K.Subcomplex)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap (e ≫ p) q K₀)]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap e (p ≫ q) K₀)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap e p K₀) := by
  let sq₁ : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e K₀.ι) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (K₀.ι ≫ e) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ p) K₀.ι) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_postcomp e K₀.ι p).symm⟩
  let sq₂ : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ p) K₀.ι)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (e ≫ p) q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (K₀.ι ≫ e ≫ p) q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ p ≫ q) K₀.ι) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_postcomp (e ≫ p) K₀.ι q).symm⟩
  let m := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.squareComparisonVerticalMap sq₁ sq₂
  have : Quasicategory (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (K₀.ι ≫ e) p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ p) K₀.ι)) :=
    inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceTarget e p K₀))
  have : Quasicategory (pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (K₀.ι ≫ e) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (K₀.ι ≫ e ≫ p) q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ p ≫ q) K₀.ι)) :=
    inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceTarget e (p ≫ q) K₀))
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison sq₂) := inferInstanceAs
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap (e ≫ p) q K₀))
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration m := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.squareComparisonVerticalMap_trivialKanFibration sq₁ sq₂
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.squareComparisonVertical_factor sq₁ sq₂
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap e p K₀ ≫ m = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap e (p ≫ q) K₀ at hf
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence m := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration m
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.trivialKanFibration_of_leftFibration_of_isQCatEquivalence
  apply hm.cancel_right
  rw [hf]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 概要：合成射に関して cocartesian な辺は、像もそうなら前半の射で cocartesian。
方針：相対 coslice の特徴づけとその充填性の消去補題を使う。
規約：前半の射は inner fibration、後半の射には充填性を仮定しない。
使われ方：底への輸送を中間の関手に関する輸送へ移す。 -/
lemma kanIsCocartesianEdge_of_comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (p : X ⟶ Y) (q : Y ⟶ Z) [InnerFibration p] (e : X _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (p ≫ q) e)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (p.app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e := by
  let a := SSet.yonedaEquiv.symm e
  have ha : SSet.yonedaEquiv a = e := Equiv.apply_symm_apply _ _
  have hap : SSet.yonedaEquiv (a ≫ p) = p.app (Opposite.op ⦋1⦌) e := by
    rw [SSet.yonedaEquiv_comp, ha]
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap a (p ≫ q) (horn 1 0)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge a (p ≫ q) (ha ▸ he)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap (a ≫ p) q (horn 1 0)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge (a ≫ p) q (hap ▸ hp)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_relativeCosliceMap_trivialKanFibration a p
    (kanRelativeCosliceMap_trivialKanFibration_cancel a p q (horn 1 0))
  rwa [ha] at h

/-- 概要：合成射に関して cartesian な辺は、像もそうなら前半の射で cartesian。
方針：全てを反転して cocartesian な消去を適用する。
規約：三つの単体集合は quasicategory、前半の射は inner fibration。
使われ方：共通の底への cartesian 輸送を制限射自体の輸送へ移す。 -/
lemma kanIsCartesianEdge_of_comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (p : X ⟶ Y) (q : Y ⟶ Z) [InnerFibration p] (e : X _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (p ≫ q) e)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q (p.app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isCocartesianEdge_op p e
  apply kanIsCocartesianEdge_of_comp (SSet.opFunctor.map p) (SSet.opFunctor.map q)
  · simpa only [← Functor.map_comp] using he.op
  · exact hp.op

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
