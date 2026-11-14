module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# 単体圏の射の先頭への頂点の追加

概要：単体圏の射に新しい初期頂点を追加し、全射・単射と合成との整合を示す。
方針：有限順序集合の零点と後続点を場合分けして写像を構成する。
規約：Segal 1974 Proposition 1.6 の自由な退化の標準単体の収縮の補助。
使われ方：全射による標準形に余分な退化を付ける。
-/

@[expose] public section
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory
open scoped _root_.Simplicial

/--
概要：単体圏の射の先頭に新しい頂点を追加する。
方針：零点を零点へ、後続点を元の像の後続点へ送る。
規約：始域・終域の次元をともに一つ増やす。
使われ方：自由な退化の標準形の全射の拡張。
-/
def simplexPrepend {m n : SimplexCategory} (θ : m ⟶ n) : ⦋m.len + 1⦌ ⟶ ⦋n.len + 1⦌ :=
  SimplexCategory.Hom.mk
    { toFun := Fin.cases 0 (fun i => (θ.toOrderHom i).succ)
      monotone' := by
        intro i j hij
        cases i using Fin.cases with
        | zero => exact Fin.zero_le _
        | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j =>
            have h := θ.toOrderHom.monotone (by
              change i.val ≤ j.val
              exact Nat.le_of_succ_le_succ hij)
            change (θ.toOrderHom i).val + 1 ≤ (θ.toOrderHom j).val + 1
            exact Nat.add_le_add_right h 1 }

/--
概要：新しい零点は零点に写る。
方針：先頭追加の定義を計算する。
規約：全ての単体圏の射に適用できる。
使われ方：収縮の新しい頂点の計算。
-/
@[simp] theorem simplexPrepend_zero {m n : SimplexCategory} (θ : m ⟶ n) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ).toOrderHom 0 = 0 := rfl

/--
概要：既存の頂点の後続点は元の像の後続点へ写る。
方針：有限順序集合の場合分けを計算する。
規約：頂点番号は一つ増える。
使われ方：面・退化との等式を各頂点で計算する。
-/
@[simp] theorem simplexPrepend_succ {m n : SimplexCategory} (θ : m ⟶ n) (i : Fin (m.len + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ).toOrderHom i.succ = (θ.toOrderHom i).succ := rfl

/--
概要：先頭追加は射の合成を保つ。
方針：零点と後続点で一致を確認する。
規約：対象の次元は一つ増える。
使われ方：像の全射・単射分解を拡張する。
-/
@[simp] theorem simplexPrepend_comp {l m n : SimplexCategory} (θ : l ⟶ m) (φ : m ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (θ ≫ φ) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend φ := by
  ext i : 3
  cases i using Fin.cases <;> rfl

/--
概要：先頭追加は恒等射を保つ。
方針：零点と後続点で定義を計算する。
規約：拡張後の次元の恒等射となる。
使われ方：全射が恒等射の標準形。
-/
@[simp] theorem simplexPrepend_id (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  ext i : 3
  cases i using Fin.cases <;> rfl

/--
概要：先頭追加は全射性を保つ。
方針：零点は零点の像、後続点は元の全射性から持ち上げる。
規約：単体圏の epi として述べる。
使われ方：拡張した標準形の全射性。
-/
instance simplexPrepend_epi {m n : SimplexCategory} (θ : m ⟶ n) [Epi θ] :
    Epi (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ) := by
  apply SimplexCategory.epi_iff_surjective.mpr
  intro j
  cases j using Fin.cases with
  | zero => exact ⟨0, rfl⟩
  | succ j =>
    obtain ⟨i, hi⟩ := SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi θ) j
    exact ⟨i.succ, congrArg Fin.succ hi⟩

/--
概要：先頭追加は単射性を保つ。
方針：零点と後続点の像は異なり、後続点同士は元の単射性で比較する。
規約：単体圏の mono として述べる。
使われ方：像の単射部分を拡張して正規化を計算する。
-/
instance simplexPrepend_mono {m n : SimplexCategory} (θ : m ⟶ n) [Mono θ] :
    Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j h
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · exact False.elim (Fin.succ_ne_zero _ h.symm)
  · exact False.elim (Fin.succ_ne_zero _ h)
  · apply congrArg Fin.succ
    apply SimplexCategory.mono_iff_injective.mp (inferInstance : Mono θ)
    exact Fin.succ_injective _ h

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend_comp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_epi (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend_epi := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_epi

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend_id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_mono (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend_mono := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_mono

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend_succ := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_succ

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend_zero := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexPrepend._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend._proof_2
