module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionObjectNaturality
public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionPinchedSpaces
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedComposition

/-!
概要：随伴の右 pinched 写像空間比較の対象変数に関する自然性。
方針：区間模型の自然性を模型比較による共役へ移す。
規約：hX・hY の射に対する自然性を h Fun の同型と実際のホモトピーで公開する。
使われ方：Kerodon Prop 6.2.1.17 の順方向の対象自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.QCatAdjunction

/-- 概要：既存の pinched 比較射は区間比較を移した射に等しい。
方針：三つの同値の合成の hom を展開する。
規約：既存の選択を変えない。
使われ方：対象自然性を既存の pinchedMap に接続する。 -/
lemma pinchedMap_eq_liftMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    a.pinchedMap x y = PinchedInterval.liftMap (a.intervalMap x y) := by
  rfl

/-- 概要：pinched の随伴比較は終域変数の射に関して自然。
方針：区間模型の自然性ホモトピーと移送の合成同型を合わせる。
規約：模型を移した後合成に関する h Fun の同型。
使われ方：写像空間の比較の終域変数自然性。 -/
noncomputable def pinchedMapNaturalityRightIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    FunctorIso
      (PinchedInterval.postcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ a.pinchedMap x y')
      (a.pinchedMap x y ≫ PinchedInterval.postcompose x ((hoFunctor.map G).toFunctor.map δ)) := by
  rw [pinchedMap_eq_liftMap, pinchedMap_eq_liftMap]
  exact (PinchedInterval.liftMapCompIso _ _) ≪≫
    PinchedInterval.liftMapIso
      (functorIsoOfSimplicialHomotopy (a.intervalMap_naturality_right x δ).some) ≪≫
    (PinchedInterval.liftMapCompIso _ _).symm

/-- 概要：pinched の随伴比較は始域変数の射に関して自然。
方針：区間模型の自然性ホモトピーと移送の合成同型を合わせる。
規約：模型を移した前合成に関する h Fun の同型。
使われ方：写像空間の比較の始域変数自然性。 -/
noncomputable def pinchedMapNaturalityLeftIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    FunctorIso
      (PinchedInterval.precompose y ((hoFunctor.map F).toFunctor.map γ) ≫ a.pinchedMap x' y)
      (a.pinchedMap x y ≫ PinchedInterval.precompose (G.app (Opposite.op ⦋0⦌) y) γ) := by
  rw [pinchedMap_eq_liftMap, pinchedMap_eq_liftMap]
  exact (PinchedInterval.liftMapCompIso _ _) ≪≫
    PinchedInterval.liftMapIso
      (functorIsoOfSimplicialHomotopy (a.intervalMap_naturality_left y γ).some) ≪≫
    (PinchedInterval.liftMapCompIso _ _).symm

/-- 概要：終域変数の自然性の実際の単体的ホモトピー。
方針：上の h Fun の同型を代表する辺を使う。
規約：逆向きも同型の逆から得られる。
使われ方：自然なホモトピー同値の順方向の可換正方形。 -/
lemma pinchedMap_naturality_right {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    Nonempty (SSet.Homotopy
      (PinchedInterval.postcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ a.pinchedMap x y')
      (a.pinchedMap x y ≫ PinchedInterval.postcompose x ((hoFunctor.map G).toFunctor.map δ))) :=
  ⟨(a.pinchedMapNaturalityRightIso x δ).simplicialHomotopy⟩

/-- 概要：始域変数の自然性の実際の単体的ホモトピー。
方針：上の h Fun の同型を代表する辺を使う。
規約：hX の任意の射に反変な正方形。
使われ方：自然なホモトピー同値の順方向の可換正方形。 -/
lemma pinchedMap_naturality_left {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    Nonempty (SSet.Homotopy
      (PinchedInterval.precompose y ((hoFunctor.map F).toFunctor.map γ) ≫ a.pinchedMap x' y)
      (a.pinchedMap x y ≫ PinchedInterval.precompose (G.app (Opposite.op ⦋0⦌) y) γ)) :=
  ⟨(a.pinchedMapNaturalityLeftIso y γ).simplicialHomotopy⟩

end SerrePositivity.InfinityCategories.QCatAdjunction
