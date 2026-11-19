module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：ホーンに欠けた面を引き戻すと、その面の境界になる。
方針：欠けた頂点を飛ばす単調埋め込みの像と、元の単体の像を比較する。
規約：全ての次元と欠けた面の位置を扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。相対三角形の境界の単射性の検査。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：欠けた面の単体がホーンへ入る条件は、その面の境界へ入ること。
方針：ホーンから欠ける別の頂点を、面の頂点へ一意に戻す。
規約：n は面の次元、d は調べる単体の次元。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。ホーンと欠けた面の交わり。 -/
theorem horn_face_mem_iff {n d : ℕ} (i : Fin (n + 2)) (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    (stdSimplex.δ i).app _ s ∈ (horn.{u} (n + 1) i).obj _ ↔
      s ∈ (boundary.{u} n).obj _ := by
  rw [mem_horn_iff_notMem_range, mem_boundary_iff_notMem_range]
  change (∃ j : Fin (n + 2), ∃ _ : j ≠ i, j ∉ Set.range (fun r => i.succAbove (s r))) ↔
    ∃ j : Fin (n + 1), j ∉ Set.range s
  constructor
  · rintro ⟨j, hj, hnot⟩
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    refine ⟨k, ?_⟩
    rintro ⟨r, hr⟩
    exact hnot ⟨r, congrArg i.succAbove hr⟩
  · rintro ⟨j, hj⟩
    refine ⟨i.succAbove j, Fin.succAbove_ne i j, ?_⟩
    rintro ⟨r, hr⟩
    exact hj ⟨r, Fin.succAbove_right_injective hr⟩

/-- 概要：ホーンの欠けた面への逆像は標準の境界部分複体。
方針：各次元の単体の所属条件を比較する。
規約：部分複体の厳密な等式。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。相対三角形の境界の pushout の構成。 -/
theorem preimage_horn_face (n : ℕ) (i : Fin (n + 2)) :
    (horn.{u} (n + 1) i).preimage (stdSimplex.δ i) = boundary.{u} n := by
  ext ⟨⟨d⟩⟩ s
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_face_mem_iff i s

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
