module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionObjectNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComposition

/-!
概要：随伴の右 pinched 写像空間比較の対象変数に関する自然性。
方針：区間模型の自然性を模型比較による共役へ移す。
規約：hX・hY の射に対する自然性を h Fun の同型と実際のホモトピーで公開する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の順方向の対象自然性。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：既存の pinched 比較射は区間比較を移した射に等しい。
方針：三つの同値の合成の hom を展開する。
規約：既存の選択を変えない。
使われ方：対象自然性を既存の pinchedMap に接続する。 -/
lemma pinchedMap_eq_liftMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    a.pinchedMap x y = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMap (a.intervalMap x y) := by
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (pinchedMap_eq_liftMap)


/-- 概要：pinched の随伴比較は終域変数の射に関して自然。
方針：区間模型の自然性ホモトピーと移送の合成同型を合わせる。
規約：模型を移した後合成に関する h Fun の同型。
使われ方：写像空間の比較の終域変数自然性。 -/
noncomputable def pinchedMapNaturalityRightIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ a.pinchedMap x y')
      (a.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose x ((hoFunctor.map G).toFunctor.map δ)) := by
  rw [pinchedMap_eq_liftMap, pinchedMap_eq_liftMap]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapCompIso _ _) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (a.intervalMap_naturality_right x δ).some) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapCompIso _ _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (pinchedMapNaturalityRightIso)


/-- 概要：pinched の随伴比較は始域変数の射に関して自然。
方針：区間模型の自然性ホモトピーと移送の合成同型を合わせる。
規約：模型を移した前合成に関する h Fun の同型。
使われ方：写像空間の比較の始域変数自然性。 -/
noncomputable def pinchedMapNaturalityLeftIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y ((hoFunctor.map F).toFunctor.map γ) ≫ a.pinchedMap x' y)
      (a.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (G.app (Opposite.op ⦋0⦌) y) γ) := by
  rw [pinchedMap_eq_liftMap, pinchedMap_eq_liftMap]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapCompIso _ _) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (a.intervalMap_naturality_left y γ).some) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapCompIso _ _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (pinchedMapNaturalityLeftIso)


/-- 概要：終域変数の自然性の実際の単体的ホモトピー。
方針：上の h Fun の同型を代表する辺を使う。
規約：逆向きも同型の逆から得られる。
使われ方：自然なホモトピー同値の順方向の可換正方形。 -/
lemma pinchedMap_naturality_right {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ a.pinchedMap x y')
      (a.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose x ((hoFunctor.map G).toFunctor.map δ))) :=
  ⟨(a.pinchedMapNaturalityRightIso x δ).simplicialHomotopy⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (pinchedMap_naturality_right)


/-- 概要：始域変数の自然性の実際の単体的ホモトピー。
方針：上の h Fun の同型を代表する辺を使う。
規約：hX の任意の射に反変な正方形。
使われ方：自然なホモトピー同値の順方向の可換正方形。 -/
lemma pinchedMap_naturality_left {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y ((hoFunctor.map F).toFunctor.map γ) ≫ a.pinchedMap x' y)
      (a.pinchedMap x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (G.app (Opposite.op ⦋0⦌) y) γ)) :=
  ⟨(a.pinchedMapNaturalityLeftIso y γ).simplicialHomotopy⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (pinchedMap_naturality_left)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
