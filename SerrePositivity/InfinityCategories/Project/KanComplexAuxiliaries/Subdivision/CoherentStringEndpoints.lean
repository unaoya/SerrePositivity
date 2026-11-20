module

public import Mathlib.AlgebraicTopology.SimplicialNerve

/-! # 合成列の二端点の標準再添字
概要：元の有限合成列の長辺を取り出す標準射と、その端点を保つ再添字の計算を行う。
方針：二点の順序圏の初点・終点の像で射を決める。
規約：長さ零と退化した合成列も含む。
使われ方：元の高次 K prism の合成列を共通の精密化パラメータ上で評価する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 合成列の二端点だけを選ぶ標準単体射。長さ零も許す。 -/
def coherentStringEndpointMap (n : ℕ) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    ⟨fun i => if i = 0 then 0 else Fin.last n, by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩

/-- 標準射の始点は元の合成列の始点。 -/
lemma coherentStringEndpointMap_first (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap n).toOrderHom 0 = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap]

/-- 標準射の終点は元の合成列の終点。 -/
lemma coherentStringEndpointMap_last (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap n).toOrderHom 1 = Fin.last n := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap]

/-- 長さ一では、元の射の二端点を選ぶ射は恒等。 -/
lemma coherentStringEndpointMap_one : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap 1 = 𝟙 ⦋1⦌ := by
  ext i
  fin_cases i <;> rfl

/-- 両端を保つ全再添字は、元の長辺を厳密に保つ。 -/
lemma coherentStringEndpointMap_comp {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (h₀ : θ.toOrderHom 0 = 0) (h₁ : θ.toOrderHom (Fin.last m) = Fin.last n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap m ≫ θ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap n := by
  apply SimplexCategory.Hom.ext_one_left
  · change θ.toOrderHom ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap m).toOrderHom 0) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first]
    exact h₀
  · change θ.toOrderHom ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap m).toOrderHom 1) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last]
    exact h₁

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
