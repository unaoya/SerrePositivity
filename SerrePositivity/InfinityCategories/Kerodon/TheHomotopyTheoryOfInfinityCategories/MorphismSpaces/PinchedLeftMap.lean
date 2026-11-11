module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberDiagramChange

/-!
概要：反転で定義した左 pinched 写像空間の作用と coslice fiber の比較の自然性。
方針：両作用を標準単体上の錐の後合成として計算する。
規約：F1 から再構成する作用は F1B 名前空間に置く。
使われ方：相対終対象性を元の右 pinched 模型の写像空間比較へ移す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLeftMap

/-- 概要：射は左 pinched 写像空間の作用を誘導する。
方針：反転した射の右 pinched 作用を再び反転する。
規約：元の始点と終点を射で写す。
使われ方：左模型の比較の自然性。 -/
def pinchedHomLeftMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (SSet.opFunctor.map f)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))

/-- 概要：固定図式の表示変更は余錐全体の値を保つ。
方針：図式の等式を消去して恒等同型へ戻す。
規約：任意の次数と終点で成立する。
使われ方：後合成の自然性の単体ごとの計算。 -/
lemma cosliceFiberDiagramIso_app_val {K Y : SSet.{u}} {a b : K ⟶ Y}
    (h : a = b) (y : Y _⦋0⦌) (n : SimplexCategoryᵒᵖ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) y).obj n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso h y).hom.app n s).val.val = s.val.val := by
  cases h
  rfl

/-- 概要：点の coslice fiber の後合成は左 pinched 比較と可換。
方針：各次数の比較を単体の値で照合する。
規約：全空間の充填性は不要。
使われ方：左右の指定 pinched 作用の同値条件を比較する。 -/
lemma cosliceFiberPinchedLeftIso_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap f x y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberPinchedLeftIso
        (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberPinchedLeftIso x y).hom ≫ pinchedHomLeftMap f x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.opObjEquiv.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  apply SSet.opObjEquiv.injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap f x y).app _ s) =
    f.app (Opposite.op ⦋n + 1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n s)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceFiberMap_eq_postcomp]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex]
  simp only [NatTrans.comp_app_apply, cosliceFiberDiagramIso_app_val]
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫
    (s.val.val ≫ f)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLeftMap
