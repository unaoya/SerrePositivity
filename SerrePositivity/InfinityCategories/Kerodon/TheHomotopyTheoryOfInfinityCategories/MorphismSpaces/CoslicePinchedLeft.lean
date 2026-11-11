module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLeftCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso

/-!
概要：既存の左 pinched 写像空間と coslice 射影の fiber の同型。
方針：両者の固定頂点・固定面の座標同値を合成し、全添字写像に対する自然性を使う。
規約：任意の単体集合に対する厳密な同型で、quasicategory 性は不要。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、Construction 5.5.2.1（Tag 01ZW）、pointed-space fiber の写像空間表示。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：coslice fiber の座標同値の逆の元の単体を計算する。
方針：座標同値の逆写像則を部分型の値で評価する。
規約：次数と二端点は固定する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、左 pinched 模型との自然性の証明。 -/
lemma cosliceFiberSimplex_equiv_symm {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (t : {s : X _⦋n + 1⦌ //
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y n).symm t) = t.val :=
  congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y n).apply_symm_apply t)

/-- 概要：左 pinched 写像空間は coslice 射影の終点上の fiber と同型。
方針：各次数の座標同値を合成し、二つの座標の同じ延長に対する自然性を使う。
規約：順方向は左 pinched 単体を join に移す。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、pointed-space fiber を既存の写像空間へ接続する。 -/
def pinchedLeftCosliceFiberIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y :=
  NatIso.ofComponents
    (fun n ↦ Equiv.toIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexEquiv x y n.unop.len).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y n.unop.len).symm)) (by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y m).injective
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex m ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y m).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexEquiv x y m) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y).map α s))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex m
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y).map α
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv x y n).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexEquiv x y n) s)))
    rw [cosliceFiberSimplex_equiv_symm]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex_naturality α.unop]
    rw [cosliceFiberSimplex_equiv_symm]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_naturality α.unop s)

/-- 概要：pointed-space 射影の fiber は 𝒮 の一点空間からの左写像空間と同型。
方針：coslice fiber と左 pinched 模型の一般の同型を適用する。
規約：元の Kan 複体との同値は coherent Hom の比較で別に証明する。
使われ方：Kerodon Construction 5.5.2.1（Tag 01ZW）、𝒮 値 unstraightening の fiber 比較。 -/
noncomputable def pointedSpaceFiberPinchedIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex s :=
  (pinchedLeftCosliceFiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex s).symm

/-- 概要：left unstraightening の fiber は 𝒮 の値への左写像空間と同型。
方針：引き戻し fiber の同型と pointed-space fiber の同型を合成する。
規約：任意の coherent な図式と底の頂点に適用する。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、元の Kan 複体との fiber 比較への帰着。 -/
noncomputable def leftUnstraighteningFiberPinchedIso {C : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) c ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex (F.app (Opposite.op ⦋0⦌) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberIso F c ≪≫
    pointedSpaceFiberPinchedIso (F.app (Opposite.op ⦋0⦌) c)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
