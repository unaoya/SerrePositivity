module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
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
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 全ての出力の有限 max 表示が実際に使う入力座標の集合。 -/
def cubeNormalFormUsedInputs {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) : Finset (Fin n) :=
  Finset.univ.biUnion (_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s)

/-- 使用入力への所属は、ある出力の support への所属。 -/
lemma mem_cubeNormalFormUsedInputs {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) (i : Fin n) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs s ↔ ∃ j, i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- 元の使用入力の昇順の標準列挙。 -/
def cubeNormalFormInputEmbedding {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) :
    Fin (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs s).card ↪o Fin n :=
  (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs s).orderEmbOfFin rfl

/-- 元の使用入力の標準列挙は、各出力の support を全て含む。 -/
lemma cubeNormalFormInputEmbedding_covers {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (j : Fin m) (i : Fin n) (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j) :
    i ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding, Finset.range_orderEmbOfFin]
  exact (_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeNormalFormUsedInputs s i).mpr ⟨j, hi⟩

/-- 使用しない入力を削除した元の有限 max 表示。 -/
def cubeNormalFormCompressed {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs s).card m :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormRestrict s (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s)

/-- 元の表示の評価は、使用入力の選択の後で圧縮表示を評価したもの。 -/
lemma cubeNormalFormCompressed_eval {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed s)
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s) x) =
        _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormRestrict_eval s _ (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding_covers s) x

/-- 使用入力の標準列挙による選択は、座標削除だけで実現される。 -/
lemma cubeNormalFormInputEmbedding_deletionGenerated {n m : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Kan.CubeDeletionGenerated (_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s)) :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect_deletionGenerated _ (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s).strictMono

/-- 圧縮表示には未使用の入力が残らない。 -/
lemma cubeNormalFormCompressed_no_unused {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs s).card) :
    ∃ j, i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed s) j := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs s :=
    Finset.orderEmbOfFin_mem _ rfl i
  obtain ⟨j, hj⟩ := (_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeNormalFormUsedInputs s _).mp hi
  exact ⟨j, (_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeJoinNormalFormRestrict_support s _ i j).mpr hj⟩

/-- 具体的な cubical 射を、元の入力選択と圧縮表示の評価として回収する。 -/
lemma concreteCubeNormalForm_compressed_eval {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube} (f : X ⟶ Y)
    (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex X.dimension) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f))
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)) x) =
        f.val x :=
  (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed_eval _ x).trans (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_eval f x)

/-- 元の具体射の圧縮表示も、元の出力順に入力が厳密に並ぶ。 -/
lemma concreteCubeNormalForm_compressed_ordered {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube} (f : X ⟶ Y)
    {j k : Fin Y.dimension} (hjk : j < k)
    {i l : Fin (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)).card}
    (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)) j)
    (hl : l ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)) k) :
    i < l := by
  apply (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)).strictMono.lt_iff_lt.mp
  exact _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_support_ordered f hjk
    ((_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeJoinNormalFormRestrict_support _ _ i j).mp hi)
    ((_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeJoinNormalFormRestrict_support _ _ l k).mp hl)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_compressed_eval := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_compressed_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_compressed_ordered := _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_compressed_ordered

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed_eval := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed_no_unused := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed_no_unused

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding_covers := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding_covers

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding_deletionGenerated := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding_deletionGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormUsedInputs := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.mem_cubeNormalFormUsedInputs := _root_.SerrePositivity.InfinityCategories.Kan.mem_cubeNormalFormUsedInputs

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputEmbedding.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormUsedInputs.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormUsedInputs.eq_1
