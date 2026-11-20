module


public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：欠ける面の境界からホーンへの標準の射。
方針：境界単体が欠く頂点を coface で移し、ホーンの既知の面に入ることを示す。
規約：正次数の面の境界。Kan 性は不要。
使われ方：Goerss–Jardine I §7、VIII §1。ホーン充填の欠ける面の相対ホモトピー。
-/

@[expose] public section
universe u
open CategoryTheory SSet Opposite
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 欠ける正次数の面の境界は、ホーンの中に入る。 -/
lemma boundaryFace_range_le_horn (n : ℕ) (i : Fin (n + 3)) :
    Subcomplex.range ((boundary.{u} (n + 1)).ι ≫ stdSimplex.δ i) ≤ horn (n + 2) i := by
  rintro ⟨⟨d⟩⟩ z hz
  obtain ⟨v, rfl⟩ := hz
  obtain ⟨k, hk⟩ := (mem_boundary_iff_notMem_range v.val).1 v.property
  rw [mem_horn_iff_notMem_range]
  refine ⟨i.succAbove k, Fin.succAbove_ne _ _, ?_⟩
  rintro ⟨a, ha⟩
  apply hk
  refine ⟨a, ?_⟩
  apply Fin.succAbove_right_injective
  change i.succAbove (v.val a) = i.succAbove k at ha
  exact ha

/-- 欠ける面の境界をホーンへ含める標準の因子分解。 -/
def boundaryToHorn (n : ℕ) (i : Fin (n + 3)) :
    (boundary.{u} (n + 1) : SSet.{u}) ⟶ (horn.{u} (n + 2) i : SSet.{u}) :=
  Subcomplex.lift ((boundary (n + 1)).ι ≫ stdSimplex.δ i) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryFace_range_le_horn n i)

/-- ホーンの包含を合成すると、欠ける面の境界の通常の包含。 -/
@[reassoc (attr := simp)]
lemma boundaryToHorn_ι (n : ℕ) (i : Fin (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryToHorn.{u} n i ≫ (horn (n + 2) i).ι =
      (boundary (n + 1)).ι ≫ stdSimplex.δ i := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
