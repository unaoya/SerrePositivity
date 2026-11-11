module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeInputFactorization

/-! # 有限座標写像の fiber ごとの max
概要：有限座標写像の各 fiber の max と、その元の関数合成との整合性を構成する。
方針：有限 max が真である条件を入力の存在で表し、二重 fiber を一重へ移す。
規約：空 fiber は零。使われ方：順序を保つ全射の隣接 connection による実現。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 元の座標写像の各 fiber にわたる入力の有限 max。 -/
def cubeFiberMax {n m : ℕ} (q : Fin n → Fin m) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert q

/-- fiber max が真であることは、その同じ fiber に真の入力があること。 -/
lemma cubeFiberMax_true_iff {n m : ℕ} (q : Fin n → Fin m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (j : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q x j = true ↔ ∃ i, q i = j ∧ x i = true :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_true_iff q x j

/-- 元の恒等座標写像の fiber max は恒等関数。 -/
lemma cubeFiberMax_id (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (_root_.id : Fin n → Fin n) = _root_.id := by
  funext x
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_insert _root_.id Function.injective_id x

/-- 座標写像の元の合成の fiber max は、同じ二つの fiber max の合成。 -/
lemma cubeFiberMax_comp {n m k : ℕ} (q : Fin n → Fin m) (r : Fin m → Fin k) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (r ∘ q) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax r ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q := by
  funext x j
  apply Bool.eq_iff_iff.mpr
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (r ∘ q) x j = true ↔ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax r (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q x) j = true
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨q i, hi, i, rfl, hx⟩
  · rintro ⟨a, ha, i, hi, hx⟩
    exact ⟨i, hi ▸ ha, hx⟩

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax_true_iff := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff
