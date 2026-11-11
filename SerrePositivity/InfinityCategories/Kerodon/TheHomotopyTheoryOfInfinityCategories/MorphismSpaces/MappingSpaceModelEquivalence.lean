module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftIntervalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右の pinched 写像空間と coslice fiber の同値。
方針：両側の区間比較の同値を合成し、左模型には既存の coslice fiber の同型を使う。
規約：始点 x と終点 y の順序は全ての模型で共通。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、coherent nerve の左写像空間の値の回収。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左 pinched 模型の既存の区間比較射は圏同値。
方針：coslice fiber との同型の逆と、coslice fiber の区間比較の同値を合成する。
規約：比較射を新しく選び直さず既存の射の性質を示す。
使われ方：Kerodon §4.6.6（Tag 04HY）、左右の写像空間の共通模型。 -/
@[kerodon 01L5]
lemma pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace x y) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberPinchedLeftIso x y).symm).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_isQCatEquivalence x y)

/-- 概要：左 pinched 写像空間と右 pinched 写像空間は同値。
方針：左から区間模型への同値と、右からの比較の逆を合成する。
規約：逆の選択を含む明示的な圏同値を返す。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、left unstraightening の fiber の同定。 -/
noncomputable def pinchedHomLeftRightEquivalence {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :=
  (pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence x y).choose.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).choose.symm

/-- 概要：coslice fiber と右 pinched 写像空間は同値。
方針：coslice fiber の区間比較と、右模型の区間比較の逆を合成する。
規約：coslice の基点は x、fiber の底は y。
使われ方：Kerodon §4.6.6（Tag 04HY）、coslice fiber を豊穣 Hom と比較する中継。 -/
noncomputable def cosliceFiberRightMappingEquivalence {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_isQCatEquivalence x y).choose.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).choose.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
