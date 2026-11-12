module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoslicePinchedLeft
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLeftCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-! # 左写像空間の連結成分の頂点での計算

概要：左 pinched 模型の Hom 同値は零単体の表す実際の辺のホモトピー類を与える。
方針：二つの反転とホモトピー圏の比較を辺の生成元で計算する。
規約：選択した合成や始対象を使わない。使われ方：余極限余錐の変更と Hom 表示の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

/-- 概要：ホモトピー圏の反転 Hom 同値は辺の類を反転した辺の類へ移す。
方針：辺の類から道への比較関手の Hom 同値とその逆を消す。
規約：辺は二切断で指定する。使われ方：左写像空間の頂点の計算。 -/
lemma stableHomotopyCategoryOpHomEquiv_homMk {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopyCategoryOpHomEquiv x y (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).fullyFaithfulFunctor.homEquiv
    (X := HomotopyCategory₂.mk (A := (truncation 2).obj X) x)
    (Y := HomotopyCategory₂.mk (A := (truncation 2).obj X) y)
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X.op).fullyFaithfulFunctor.homEquiv
    (X := HomotopyCategory₂.mk (A := (truncation 2).obj X.op) (SSet.opObjEquiv.symm y))
    (Y := HomotopyCategory₂.mk (A := (truncation 2).obj X.op) (SSet.opObjEquiv.symm x))
  exact congrArg (fun t => b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopyCategory₂OpHomEquiv x y t))
    (a.symm_apply_apply (HomotopyCategory₂.homMk e))

/-- 概要：左 pinched 模型の零単体は指定した両端を持つ辺を与える。
方針：元の一次単体を取り、固定始点と固定面の条件を読む。
規約：二切断の辺として表示する。使われ方：連結成分の具体的な計算。 -/
def stablePinchedLeftVertexEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋0⦌) : Edge (X := (truncation 2).obj X) x y where
  edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal 0 s
  src_eq := by
    change X.map (SimplexCategory.δ (1 : Fin 2)).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal 0 s) = x
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_source 0 s
    rw [show SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ 1 by decide] at h
    exact h
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_target 0 s).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y)

/-- 概要：左 pinched 模型の零単体の連結成分は対応する辺のホモトピー類を与える。
方針：反転した右模型での計算を反転 Hom 同値の単射性で戻す。
規約：辺は右模型からの反転で表す。使われ方：coslice の具体的な辺との照合。 -/
lemma stablePinchedHomLeftPiZeroEquiv_mk {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv x y (SSet.π₀.mk s) =
      SSet.Truncated.HomotopyCategory.homMk (stablePinchedLeftVertexEdge s) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopyCategoryOpHomEquiv x y).injective
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (stablePinchedLeftVertexEdge s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) (SSet.opObjEquiv s) := by
    apply SSet.Truncated.Edge.ext
    rfl
  rw [stableHomotopyCategoryOpHomEquiv_homMk (stablePinchedLeftVertexEdge s), he]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- 概要：coslice fiber の頂点の左写像空間による Hom 表示は対応する辺の類。
方針：座標同値を零次で展開し、二点の join の標準辺を比較する。
規約：固定図式は始点の Yoneda 表示。使われ方：表現可能な比較の代表元での計算。 -/
lemma stableCosliceFiberPiZeroEquiv_mk {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv x y
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso x y).inv (SSet.π₀.mk s)) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberVertexToEdge s).toTruncated := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv x y
    (SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso x y).inv.app (Opposite.op ⦋0⦌) s)) = _
  rw [stablePinchedHomLeftPiZeroEquiv_mk]
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries
