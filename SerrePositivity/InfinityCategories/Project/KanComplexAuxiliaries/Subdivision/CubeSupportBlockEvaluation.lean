module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeSupportBlockMap

/-! # support ブロックの max と元の具体射の非定数出力
概要：ブロックの fiber max が元の有限 max 表示の空でない出力を厳密に回収する。
方針：fiber の所属の同定を有限 max の存在条件へ適用し、実際の射へ束ねる。
規約：定数出力の挿入と Serre 語評価の降下は別工程。使われ方：正規化の max 工程。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 各ブロックの fiber max は、元の同じ空でない出力の評価。 -/
lemma cubeSupportBlockMap_eval {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
    (a : Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h) x a =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval s x (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s a) := by
  have ha : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s a)).Nonempty :=
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeSupportNonemptyOutputs s _).mp (Finset.orderEmbOfFin_mem _ rfl a)
  cases hs : s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s a) with
  | none => simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport, hs] at ha
  | some t =>
    apply Bool.eq_iff_iff.mpr
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_fiber, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport, hs, Option.getD_some,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval]
    change (∃ i, i ∈ t ∧ x i = ⊤) ↔ t.sup x = ⊤
    exact Finset.sup_eq_top_iff.symm

/-- 元の空でない出力の昇順列挙による、実際の座標選択。 -/
def cubeSupportOutputSelection {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s),
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_generated _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s).strictMono⟩

/-- 元の support ブロックの max を取る実際の具体的な射。 -/
def cubeSupportMax {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m} (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition s) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportNonemptyOutputs s).card :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap h),
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeConnectionGenerated_generated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_connectionGenerated h)⟩

/-- 元の具体射の空でない出力への射影は、同じ support ブロックの max そのもの。 -/
lemma cubeSupportMax_eq_projection {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportMax h = f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSelection (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) := by
  apply Subtype.ext
  funext x a
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_eval h x a).trans
    (congrFun (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval f x) _)

/-- 入力削除後の元の残余射の support は、順序つきで全入力を尽くす。 -/
lemma concreteCubeInputCompressedSupportPartition {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f)) where
  ordered := by
    intro j k hjk i l hi hl
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_support_ordered (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f) hjk hi hl
  covers := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_no_unused f

/-- 入力削除後の残余射の空でない出力は、隣接 connection のみで実現される。 -/
lemma concreteCubeInputCompressed_projection_connectionGenerated {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeConnectionGenerated
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputSelection
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f))).val) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportMax_eq_projection (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressedSupportPartition f)]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_connectionGenerated _

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
