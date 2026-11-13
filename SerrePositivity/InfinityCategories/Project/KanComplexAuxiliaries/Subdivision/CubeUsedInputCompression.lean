module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeNormalFormRestriction
public import Mathlib.Data.Finset.Sort

/-! # 元の使用入力だけへの有限 max 表示の圧縮
概要：全出力の support の和集合を昇順に列挙し、未使用入力を削除した表示へ移す。
方針：有限順序集合の標準列挙と、座標制限の評価回収を適用する。
規約：ここでの残余表示の比較は頂点関数の等号。使われ方：正規化の削除工程。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 全ての出力の有限 max 表示が実際に使う入力座標の集合。 -/
def cubeNormalFormUsedInputs {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) : Finset (Fin n) :=
  Finset.univ.biUnion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s)

/-- 使用入力への所属は、ある出力の support への所属。 -/
lemma mem_cubeNormalFormUsedInputs {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) (i : Fin n) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s ↔ ∃ j, i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- 元の使用入力の昇順の標準列挙。 -/
def cubeNormalFormInputEmbedding {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).card ↪o Fin n :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).orderEmbOfFin rfl

/-- 元の使用入力の標準列挙は、各出力の support を全て含む。 -/
lemma cubeNormalFormInputEmbedding_covers {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (j : Fin m) (i : Fin n) (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j) :
    i ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding, Finset.range_orderEmbOfFin]
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeNormalFormUsedInputs s i).mpr ⟨j, hi⟩

/-- 使用しない入力を削除した元の有限 max 表示。 -/
def cubeNormalFormCompressed {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).card m :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormRestrict s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s)

/-- 元の表示の評価は、使用入力の選択の後で圧縮表示を評価したもの。 -/
lemma cubeNormalFormCompressed_eval {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed s)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s) x) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval s x :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormRestrict_eval s _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding_covers s) x

/-- 使用入力の標準列挙による選択は、座標削除だけで実現される。 -/
lemma cubeNormalFormInputEmbedding_deletionGenerated {n m : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_deletionGenerated _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s).strictMono

/-- 圧縮表示には未使用の入力が残らない。 -/
lemma cubeNormalFormCompressed_no_unused {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).card) :
    ∃ j, i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed s) j := by
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s :=
    Finset.orderEmbOfFin_mem _ rfl i
  obtain ⟨j, hj⟩ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeNormalFormUsedInputs s _).mp hi
  exact ⟨j, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormRestrict_support s _ i j).mpr hj⟩

/-- 具体的な cubical 射を、元の入力選択と圧縮表示の評価として回収する。 -/
lemma concreteCubeNormalForm_compressed_eval {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)) x) =
        f.val x :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_eval _ x).trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval f x)

/-- 元の具体射の圧縮表示も、元の出力順に入力が厳密に並ぶ。 -/
lemma concreteCubeNormalForm_compressed_ordered {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    {j k : Fin Y.dimension} (hjk : j < k)
    {i l : Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)).card}
    (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)) j)
    (hl : l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)) k) :
    i < l := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)).strictMono.lt_iff_lt.mp
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_support_ordered f hjk
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormRestrict_support _ _ i j).mp hi)
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormRestrict_support _ _ l k).mp hl)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_compressed_eval := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_compressed_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_compressed_ordered := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_compressed_ordered

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed_eval := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed_no_unused := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_no_unused

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding_covers := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding_covers

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding_deletionGenerated := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding_deletionGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormUsedInputs := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.mem_cubeNormalFormUsedInputs := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeNormalFormUsedInputs

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormUsedInputs.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs.eq_1
