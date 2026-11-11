module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeOrderedNormalForm

/-! # 具体的な cubical 合成の support の計算
概要：合成の support を、中間座標の support の有限和集合から回収する。
方針：合成出力が定数一になる場合を分離し、有効入力の中間座標の両方向を証明する。
規約：一端点の吸収を保持する。使われ方：正準生成語と Serre 作用の合成比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 合成の有効入力は、非定数一条件と有効な中間座標で特徴づけられる。 -/
lemma cubeMapGenerated_active_comp_iff {n m k : ℕ}
    {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k}
    (hg : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated g) (i : Fin n) (j : Fin k) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (g ∘ f) i j ↔ g (f ⊥) j = false ∧
      ∃ a, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i a ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive g a j := by
  constructor
  · intro h
    exact ⟨h.1, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_active_comp hg h⟩
  · rintro ⟨hzero, a, hfa, hga⟩
    refine ⟨hzero, ?_⟩
    have hle := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_monotone hg
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeVertexAtom_le (f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i)) a hfa.2) j
    rw [hga.2] at hle
    exact Bool.eq_true_of_true_le hle

/-- 元の合成の support は、定数一への吸収または中間 support の有限和集合。 -/
lemma concreteCubeNormalForm_support_comp {X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : Fin Z.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (f ≫ g)) j =
      if g.val (f.val ⊥) j = true then ∅ else
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm g) j).biUnion
          (fun a => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) a) := by
  apply Finset.ext
  intro i
  change i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap (g.val ∘ f.val)) j ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormSupport, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_active_comp_iff g.property]
  cases g.val (f.val ⊥) j <;>
    simp [ Finset.mem_biUnion, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormSupport,
      and_comm]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeNormalForm_support_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_support_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_active_comp_iff := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_active_comp_iff
