module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Set.Defs
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryNormalization

/-!
概要：ホーン上で定数の境界の充填を最後の面のホモトピー類へ還元する。
方針：最後の面を PtSimplex として取り出し、定数単体との RelStruct を充填に使う。
規約：零次数の PtSimplex も含む。追加の消滅公理を導入しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。acyclic Kan 複体の境界充填。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.BoundaryNormalization
end SerrePositivity.KST.Spectra.BoundaryNormalization
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.BoundaryNormalization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：境界内の最後の面と他の面の二重制限を交換する。
方針：標準単体へ含めて二つの面の交換公式を使う。
規約：二重制限の次元は n。
使われ方：Goerss–Jardine I §7。最後の面の境界が定数であることの検査。 -/
theorem last_face_exchange (n : ℕ) (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ boundary.ι.{u} (Fin.last (n + 2)) =
      stdSimplex.δ (Fin.last (n + 1)) ≫ boundary.ι j.castSucc := by
  apply (cancel_mono (boundary (n + 2)).ι).1
  simp only [Category.assoc, boundary.ι_ι]
  exact stdSimplex.δ_comp_δ' (Fin.castSucc_lt_last j)

/-- 概要：ホーン上で定数の境界射の最後の面は境界定数単体。
方針：二つの面の交換で最後の面の境界を他の面の定数値へ移す。
規約：次数 n=0 では境界が空である。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界のホモトピー類の代表。 -/
def lastSimplex {X : SSet.{u}} (n : ℕ) (x : X _⦋0⦌)
    (g : (boundary.{u} (n + 1) : SSet.{u}) ⟶ X)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion n ≫ g = SSet.const x) : X.PtSimplex n x where
  map := boundary.ι (Fin.last (n + 1)) ≫ g
  comm := by
    simp only [Subcomplex.ofSimplex_ι, SSet.comp_const]
    cases n with
    | zero => exact boundary.hom_ext₀
    | succ n =>
      apply boundary.hom_ext
      intro j
      simp only [boundary.ι_ι_assoc, SSet.comp_const]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.last_face_exchange, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.normalized_face (n + 1) x g hg j.castSucc (Fin.castSucc_ne_last j), SSet.comp_const]

/-- 概要：正規化した境界の最後の面の類が基点なら全境界を充填できる。
方針：定数単体と最後の面を隣接二面に持つ RelStruct を選び、各面で比較する。
規約：全自然数次数のホモトピー類の界面を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。消滅から実際の充填への変換。 -/
theorem exists_filler_of_lastSimplex {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (x : X _⦋0⦌) (g : (boundary.{u} (n + 1) : SSet.{u}) ⟶ X)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion n ≫ g = SSet.const x)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lastSimplex n x g hg) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n) :
    ∃ s : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ s = g := by
  have hrel : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (RelativeMorphism.const : X.PtSimplex n x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lastSimplex n x g hg) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk_const n).trans h.symm
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n _ _ (Fin.last n)).1 hrel
  refine ⟨r.map, ?_⟩
  apply boundary.hom_ext
  intro j
  rw [boundary.ι_ι_assoc]
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    exact r.δ_succ_map
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.normalized_face n x g hg j hj]
    by_cases hj' : j = (Fin.last n).castSucc
    · subst j
      exact r.δ_castSucc_map
    · apply r.δ_map_of_lt
      have h₁ : j.val ≠ n + 1 := fun h ↦ hj (Fin.ext h)
      have h₂ : j.val ≠ n := fun h ↦ hj' (Fin.ext h)
      change j.val < n
      omega

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryNormalization.exists_filler_of_lastSimplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_filler_of_lastSimplex

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lastSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryNormalization.lastSimplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lastSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryNormalization.last_face_exchange := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.last_face_exchange

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.BoundaryNormalization.lastSimplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lastSimplex._proof_1
