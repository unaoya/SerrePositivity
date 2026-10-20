module
public import SerrePositivity.KST.SConstruction.CubeSupportBlockMap

/-! # support ブロックの max と元の具体射の非定数出力
概要：ブロックの fiber max が元の有限 max 表示の空でない出力を厳密に回収する。
方針：fiber の所属の同定を有限 max の存在条件へ適用し、実際の射へ束ねる。
規約：定数出力の挿入と Serre 語評価の降下は別工程。使われ方：正規化の max 工程。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 各ブロックの fiber max は、元の同じ空でない出力の評価。 -/
lemma cubeSupportBlockMap_eval {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) (x : CubeVertex n)
    (a : Fin (cubeSupportNonemptyOutputs s).card) :
    cubeFiberMax (cubeSupportBlockMap h) x a =
      cubeJoinNormalFormEval s x (cubeSupportOutputEmbedding s a) := by
  have ha : (cubeJoinNormalFormSupport s (cubeSupportOutputEmbedding s a)).Nonempty :=
    (mem_cubeSupportNonemptyOutputs s _).mp (Finset.orderEmbOfFin_mem _ rfl a)
  cases hs : s (cubeSupportOutputEmbedding s a) with
  | none => simp [cubeJoinNormalFormSupport, hs] at ha
  | some t =>
    apply Bool.eq_iff_iff.mpr
    rw [cubeFiberMax_true_iff]
    simp only [cubeSupportBlockMap_fiber, cubeJoinNormalFormSupport, hs, Option.getD_some,
      cubeJoinNormalFormEval, cubeJoinTermEval]
    change (∃ i, i ∈ t ∧ x i = ⊤) ↔ t.sup x = ⊤
    exact Finset.sup_eq_top_iff.symm

/-- 元の空でない出力の昇順列挙による、実際の座標選択。 -/
def cubeSupportOutputSelection {n m : ℕ} (s : CubeJoinNormalForm n m) :
    ConcreteCube.mk m ⟶ ConcreteCube.mk (cubeSupportNonemptyOutputs s).card :=
  ⟨cubeCoordinateSelect (cubeSupportOutputEmbedding s),
    cubeCoordinateSelect_generated _ (cubeSupportOutputEmbedding s).strictMono⟩

/-- 元の support ブロックの max を取る実際の具体的な射。 -/
def cubeSupportMax {n m : ℕ} {s : CubeJoinNormalForm n m} (h : CubeSupportPartition s) :
    ConcreteCube.mk n ⟶ ConcreteCube.mk (cubeSupportNonemptyOutputs s).card :=
  ⟨cubeFiberMax (cubeSupportBlockMap h),
    cubeConnectionGenerated_generated (cubeSupportBlockMap_connectionGenerated h)⟩

/-- 元の具体射の空でない出力への射影は、同じ support ブロックの max そのもの。 -/
lemma cubeSupportMax_eq_projection {X Y : ConcreteCube} (f : X ⟶ Y)
    (h : CubeSupportPartition (concreteCubeNormalForm f)) :
    cubeSupportMax h = f ≫ cubeSupportOutputSelection (concreteCubeNormalForm f) := by
  apply Subtype.ext
  funext x a
  exact (cubeSupportBlockMap_eval h x a).trans
    (congrFun (concreteCubeNormalForm_eval f x) _)

/-- 入力削除後の元の残余射の support は、順序つきで全入力を尽くす。 -/
lemma concreteCubeInputCompressedSupportPartition {X Y : ConcreteCube} (f : X ⟶ Y) :
    CubeSupportPartition (concreteCubeNormalForm (concreteCubeInputCompressed f)) where
  ordered := by
    intro j k hjk i l hi hl
    exact concreteCubeNormalForm_support_ordered (concreteCubeInputCompressed f) hjk hi hl
  covers := concreteCubeInputCompressed_no_unused f

/-- 入力削除後の残余射の空でない出力は、隣接 connection のみで実現される。 -/
lemma concreteCubeInputCompressed_projection_connectionGenerated {X Y : ConcreteCube}
    (f : X ⟶ Y) : CubeConnectionGenerated
      ((concreteCubeInputCompressed f ≫ cubeSupportOutputSelection
        (concreteCubeNormalForm (concreteCubeInputCompressed f))).val) := by
  rw [← cubeSupportMax_eq_projection (concreteCubeInputCompressed f)
    (concreteCubeInputCompressedSupportPartition f)]
  exact cubeSupportBlockMap_connectionGenerated _

end SerrePositivity.KST.SConstruction
