module
public import SerrePositivity.InfinityCategories.Kan.CubeNormalFormRestriction
public import Mathlib.Data.Finset.Sort

/-! # 元の使用入力だけへの有限 max 表示の圧縮
概要：全出力の support の和集合を昇順に列挙し、未使用入力を削除した表示へ移す。
方針：有限順序集合の標準列挙と、座標制限の評価回収を適用する。
規約：ここでの残余表示の比較は頂点関数の等号。使われ方：正規化の削除工程。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 全ての出力の有限 max 表示が実際に使う入力座標の集合。 -/
def cubeNormalFormUsedInputs {n m : ℕ} (s : CubeJoinNormalForm n m) : Finset (Fin n) :=
  Finset.univ.biUnion (cubeJoinNormalFormSupport s)

/-- 使用入力への所属は、ある出力の support への所属。 -/
lemma mem_cubeNormalFormUsedInputs {n m : ℕ} (s : CubeJoinNormalForm n m) (i : Fin n) :
    i ∈ cubeNormalFormUsedInputs s ↔ ∃ j, i ∈ cubeJoinNormalFormSupport s j := by
  simp only [cubeNormalFormUsedInputs, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- 元の使用入力の昇順の標準列挙。 -/
def cubeNormalFormInputEmbedding {n m : ℕ} (s : CubeJoinNormalForm n m) :
    Fin (cubeNormalFormUsedInputs s).card ↪o Fin n :=
  (cubeNormalFormUsedInputs s).orderEmbOfFin rfl

/-- 元の使用入力の標準列挙は、各出力の support を全て含む。 -/
lemma cubeNormalFormInputEmbedding_covers {n m : ℕ} (s : CubeJoinNormalForm n m)
    (j : Fin m) (i : Fin n) (hi : i ∈ cubeJoinNormalFormSupport s j) :
    i ∈ Set.range (cubeNormalFormInputEmbedding s) := by
  rw [cubeNormalFormInputEmbedding, Finset.range_orderEmbOfFin]
  exact (mem_cubeNormalFormUsedInputs s i).mpr ⟨j, hi⟩

/-- 使用しない入力を削除した元の有限 max 表示。 -/
def cubeNormalFormCompressed {n m : ℕ} (s : CubeJoinNormalForm n m) :
    CubeJoinNormalForm (cubeNormalFormUsedInputs s).card m :=
  cubeJoinNormalFormRestrict s (cubeNormalFormInputEmbedding s)

/-- 元の表示の評価は、使用入力の選択の後で圧縮表示を評価したもの。 -/
lemma cubeNormalFormCompressed_eval {n m : ℕ} (s : CubeJoinNormalForm n m)
    (x : CubeVertex n) :
    cubeJoinNormalFormEval (cubeNormalFormCompressed s)
      (cubeCoordinateSelect (cubeNormalFormInputEmbedding s) x) =
        cubeJoinNormalFormEval s x :=
  cubeJoinNormalFormRestrict_eval s _ (cubeNormalFormInputEmbedding_covers s) x

/-- 使用入力の標準列挙による選択は、座標削除だけで実現される。 -/
lemma cubeNormalFormInputEmbedding_deletionGenerated {n m : ℕ}
    (s : CubeJoinNormalForm n m) :
    CubeDeletionGenerated (cubeCoordinateSelect (cubeNormalFormInputEmbedding s)) :=
  cubeCoordinateSelect_deletionGenerated _ (cubeNormalFormInputEmbedding s).strictMono

/-- 圧縮表示には未使用の入力が残らない。 -/
lemma cubeNormalFormCompressed_no_unused {n m : ℕ} (s : CubeJoinNormalForm n m)
    (i : Fin (cubeNormalFormUsedInputs s).card) :
    ∃ j, i ∈ cubeJoinNormalFormSupport (cubeNormalFormCompressed s) j := by
  have hi : cubeNormalFormInputEmbedding s i ∈ cubeNormalFormUsedInputs s :=
    Finset.orderEmbOfFin_mem _ rfl i
  obtain ⟨j, hj⟩ := (mem_cubeNormalFormUsedInputs s _).mp hi
  exact ⟨j, (mem_cubeJoinNormalFormRestrict_support s _ i j).mpr hj⟩

/-- 具体的な cubical 射を、元の入力選択と圧縮表示の評価として回収する。 -/
lemma concreteCubeNormalForm_compressed_eval {X Y : ConcreteCube} (f : X ⟶ Y)
    (x : CubeVertex X.dimension) :
    cubeJoinNormalFormEval (cubeNormalFormCompressed (concreteCubeNormalForm f))
      (cubeCoordinateSelect (cubeNormalFormInputEmbedding (concreteCubeNormalForm f)) x) =
        f.val x :=
  (cubeNormalFormCompressed_eval _ x).trans (concreteCubeNormalForm_eval f x)

/-- 元の具体射の圧縮表示も、元の出力順に入力が厳密に並ぶ。 -/
lemma concreteCubeNormalForm_compressed_ordered {X Y : ConcreteCube} (f : X ⟶ Y)
    {j k : Fin Y.dimension} (hjk : j < k)
    {i l : Fin (cubeNormalFormUsedInputs (concreteCubeNormalForm f)).card}
    (hi : i ∈ cubeJoinNormalFormSupport (cubeNormalFormCompressed (concreteCubeNormalForm f)) j)
    (hl : l ∈ cubeJoinNormalFormSupport (cubeNormalFormCompressed (concreteCubeNormalForm f)) k) :
    i < l := by
  apply (cubeNormalFormInputEmbedding (concreteCubeNormalForm f)).strictMono.lt_iff_lt.mp
  exact concreteCubeNormalForm_support_ordered f hjk
    ((mem_cubeJoinNormalFormRestrict_support _ _ i j).mp hi)
    ((mem_cubeJoinNormalFormRestrict_support _ _ l k).mp hl)

end SerrePositivity.KST.SConstruction
