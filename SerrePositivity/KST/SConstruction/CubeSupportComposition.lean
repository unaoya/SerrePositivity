module
public import SerrePositivity.KST.SConstruction.CubeOrderedNormalForm

/-! # 具体的な cubical 合成の support の計算
概要：合成の support を、中間座標の support の有限和集合から回収する。
方針：合成出力が定数一になる場合を分離し、有効入力の中間座標の両方向を証明する。
規約：一端点の吸収を保持する。使われ方：正準生成語と Serre 作用の合成比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 合成の有効入力は、非定数一条件と有効な中間座標で特徴づけられる。 -/
lemma cubeMapGenerated_active_comp_iff {n m k : ℕ}
    {f : CubeVertex n → CubeVertex m} {g : CubeVertex m → CubeVertex k}
    (hg : CubeMapGenerated g) (i : Fin n) (j : Fin k) :
    CubeActive (g ∘ f) i j ↔ g (f ⊥) j = false ∧
      ∃ a, CubeActive f i a ∧ CubeActive g a j := by
  constructor
  · intro h
    exact ⟨h.1, cubeMapGenerated_active_comp hg h⟩
  · rintro ⟨hzero, a, hfa, hga⟩
    refine ⟨hzero, ?_⟩
    have hle := cubeMapGenerated_monotone hg
      (cubeVertexAtom_le (f (cubeVertexAtom n i)) a hfa.2) j
    rw [hga.2] at hle
    exact Bool.eq_true_of_true_le hle

/-- 元の合成の support は、定数一への吸収または中間 support の有限和集合。 -/
lemma concreteCubeNormalForm_support_comp {X Y Z : ConcreteCube}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : Fin Z.dimension) :
    cubeJoinNormalFormSupport (concreteCubeNormalForm (f ≫ g)) j =
      if g.val (f.val ⊥) j = true then ∅ else
        (cubeJoinNormalFormSupport (concreteCubeNormalForm g) j).biUnion
          (fun a => cubeJoinNormalFormSupport (concreteCubeNormalForm f) a) := by
  apply Finset.ext
  intro i
  change i ∈ cubeJoinNormalFormSupport (cubeJoinNormalFormOfMap (g.val ∘ f.val)) j ↔ _
  rw [mem_cubeJoinNormalFormSupport, cubeMapGenerated_active_comp_iff g.property]
  cases g.val (f.val ⊥) j <;>
    simp [ Finset.mem_biUnion, concreteCubeNormalForm, mem_cubeJoinNormalFormSupport,
      and_comm]

end SerrePositivity.KST.SConstruction
