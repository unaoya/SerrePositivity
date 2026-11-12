module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeJoinNormalForm

/-! # 具体的な立方体の有効入力座標
概要：定数一の出力を除いた入力 support と、その合成における中間座標を構成する。
方針：一座標頂点の順序と有限 join 回収式から、合成の有効入力の証人を取り出す。
規約：定数一は有効入力を持たない。使われ方：生成射の support の順序と非交差性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 定数一の出力を除いた、元の射の有効入力座標。 -/
def CubeActive {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) (i : Fin n) (j : Fin m) :
    Prop :=
  f ⊥ j = false ∧ f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) j = true

/-- 一座標頂点は、その座標が真である任意の頂点以下。 -/
lemma cubeVertexAtom_le {n : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (i : Fin n) (hi : x i = true) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i ≤ x := by
  intro k
  by_cases h : k = i
  · subst k
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom, hi]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom, h]

/-- join 射の非定数一の真の値は、一つの有効入力座標で検出される。 -/
lemma cubeJoinMap_exists_active {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (j : Fin m)
    (hzero : f ⊥ j = false) (htrue : f x j = true) :
    ∃ i, x i = true ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i j := by
  have hx := congrFun (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinMap_eval hf x) j
  simp only [Pi.sup_apply, Finset.sup_apply] at hx
  change f x j = f ⊥ j ⊔ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexSupport x).sup
    (fun i => f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) j) at hx
  rw [hzero] at hx
  change f x j = (⊥ : Bool) ⊔ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexSupport x).sup
    (fun i => f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) j) at hx
  rw [bot_sup_eq, htrue] at hx
  obtain ⟨i, hi, hval⟩ := Finset.sup_eq_top_iff.mp hx.symm
  exact ⟨i, (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.mem_cubeVertexSupport x i).mp hi, hzero, hval⟩

/-- 合成の有効入力は、同じ元の二関数の有効な中間座標を通る。 -/
lemma cubeMapGenerated_active_comp {n m k : ℕ}
    {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k}
    (hg : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated g) {i : Fin n} {j : Fin k}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (g ∘ f) i j) :
    ∃ a, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i a ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive g a j := by
  change g (f ⊥) j = false ∧ g (f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i)) j = true at h
  have hmono := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_monotone hg
  have hgzero : g ⊥ j = false := by
    exact Bool.eq_false_of_le_false (h.1 ▸ (hmono bot_le j))
  obtain ⟨a, ha, hga⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinMap_exists_active (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_sup hg)
    (f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i)) j hgzero h.2
  have hfzero : f ⊥ a = false := by
    cases hv : f ⊥ a with
    | false => rfl
    | true =>
      have hle := hmono (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeVertexAtom_le (f ⊥) a hv) j
      rw [hga.2, h.1] at hle
      exact Bool.noConfusion (Bool.eq_true_of_true_le hle)
  exact ⟨a, ⟨hfzero, ha⟩, hga⟩

/-- 異なる出力の有効入力が、出力順に厳密に並ぶ条件。 -/
def CubeSupportOrdered {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) : Prop :=
  ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f i j → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive f l k → i < l

/-- 有効入力の順序条件は、元の生成関数の合成で閉じる。 -/
lemma cubeSupportOrdered_comp {n m k : ℕ}
    {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k}
    (hg : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated g) (hfOrder : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered f)
    (hgOrder : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered g) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered (g ∘ f) := by
  intro j k hjk i l hi hl
  obtain ⟨a, hia, haj⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_active_comp hg hi
  obtain ⟨b, hlb, hbk⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_active_comp hg hl
  exact hfOrder (hgOrder hjk haj hbk) hia hlb

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeActive := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeSupportOrdered := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinMap_exists_active := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinMap_exists_active

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_active_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_active_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOrdered_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexAtom_le := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeVertexAtom_le
