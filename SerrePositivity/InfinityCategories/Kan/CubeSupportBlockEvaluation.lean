module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeSupportBlockMap

/-! # support ブロックの max と元の具体射の非定数出力
概要：ブロックの fiber max が元の有限 max 表示の空でない出力を厳密に回収する。
方針：fiber の所属の同定を有限 max の存在条件へ適用し、実際の射へ束ねる。
規約：定数出力の挿入と Serre 語評価の降下は別工程。使われ方：正規化の max 工程。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 各ブロックの fiber max は、元の同じ空でない出力の評価。 -/
lemma cubeSupportBlockMap_eval {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition s) (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n)
    (a : Fin (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s).card) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap h) x a =
      _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s a) := by
  have ha : (_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s a)).Nonempty :=
    (_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeSupportNonemptyOutputs s _).mp (Finset.orderEmbOfFin_mem _ rfl a)
  cases hs : s (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s a) with
  | none => simp [_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport, hs] at ha
  | some t =>
    apply Bool.eq_iff_iff.mpr
    rw [_root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_true_iff]
    simp only [_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap_fiber, _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport, hs, Option.getD_some,
      _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval, _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinTermEval]
    change (∃ i, i ∈ t ∧ x i = ⊤) ↔ t.sup x = ⊤
    exact Finset.sup_eq_top_iff.symm

/-- 元の空でない出力の昇順列挙による、実際の座標選択。 -/
def cubeSupportOutputSelection {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s).card :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s),
    _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect_generated _ (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s).strictMono⟩

/-- 元の support ブロックの max を取る実際の具体的な射。 -/
def cubeSupportMax {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m} (h : _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition s) :
    _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s).card :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap h),
    _root_.SerrePositivity.InfinityCategories.Kan.cubeConnectionGenerated_generated (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap_connectionGenerated h)⟩

/-- 元の具体射の空でない出力への射影は、同じ support ブロックの max そのもの。 -/
lemma cubeSupportMax_eq_projection {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube} (f : X ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax h = f ≫ _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputSelection (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f) := by
  apply Subtype.ext
  funext x a
  exact (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap_eval h x a).trans
    (congrFun (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_eval f x) _)

/-- 入力削除後の元の残余射の support は、順序つきで全入力を尽くす。 -/
lemma concreteCubeInputCompressedSupportPartition {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed f)) where
  ordered := by
    intro j k hjk i l hi hl
    exact _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_support_ordered (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed f) hjk hi hl
  covers := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed_no_unused f

/-- 入力削除後の残余射の空でない出力は、隣接 connection のみで実現される。 -/
lemma concreteCubeInputCompressed_projection_connectionGenerated {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube}
    (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated
      ((_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed f ≫ _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputSelection
        (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed f))).val) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_eq_projection (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed f)
    (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressedSupportPartition f)]
  exact _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap_connectionGenerated _

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputCompressedSupportPartition := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressedSupportPartition

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputCompressed_projection_connectionGenerated := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed_projection_connectionGenerated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportBlockMap_eval := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap_eval

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportMax := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportMax_eq_projection := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_eq_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputSelection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOutputSelection := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputSelection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportMax._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOutputSelection._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputSelection._proof_1
