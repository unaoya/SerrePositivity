module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.Unique
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AcyclicFiber
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryNormalization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.NormalizedBoundaryFilling

/-!
概要：非空な Kan 複体の全ホモトピー類の消滅から、全ての単射への終対象射の RLP を導く。
方針：境界を正規化し、最後の面の類を消して充填した後、元の境界へホモトピーで戻す。
規約：全基点と零次数を含む。Kan–Quillen モデル構造の存在は使わない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）、BF 1978 §2。Whitehead の充填による証明。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：非空な Kan 複体の全ホモトピー類が一元なら任意の境界を充填できる。
方針：正次元では最後のホーンの正規化、零次元では指定頂点を使う。
規約：n は充填する標準単体の次元。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。acyclic Kan 複体の境界 RLP。 -/
theorem exists_boundary_filler_of_homotopySubsingleton {X : SSet.{u}} [KanComplex X]
    (x₀ : X _⦋0⦌) (hπ : ∀ (x : X _⦋0⦌) (n : ℕ), Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x))
    (n : ℕ) (f : (boundary.{u} n : SSet.{u}) ⟶ X) :
    ∃ s : (Δ[n] : SSet.{u}) ⟶ X, (boundary n).ι ≫ s = f := by
  cases n with
  | zero => exact ⟨SSet.const x₀, boundary.hom_ext₀⟩
  | succ n =>
    obtain ⟨x, g, hg, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_normalization n f
    have hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lastSimplex n x g hg) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := (hπ x n).elim _ _
    obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_filler_of_lastSimplex n x g hg hlast
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_filler_of_homotopy (n + 1) f g H s hs

/-- 概要：上の非空な Kan 複体の終対象への射は全ての単射に RLP を持つ。
方針：境界での充填を、単射の境界 cell 分解に対する RLP の閉性へ移す。
規約：終対象射の弱同値性やモデル構造の公理を仮定しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。任意の源からの実際の収縮と持ち上げ。 -/
theorem terminal_rlp_of_homotopySubsingleton {X : SSet.{u}} [KanComplex X]
    (x₀ : X _⦋0⦌) (hπ : ∀ (x : X _⦋0⦌) (n : ℕ), Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from X) := by
  rw [SSet.rlp_monomorphisms]
  intro A B i hi
  rcases hi with ⟨n⟩
  constructor
  intro a b _sq
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_boundary_filler_of_homotopySubsingleton x₀ hπ n a
  exact CommSq.HasLift.mk' { l := s, fac_left := hs, fac_right := Subsingleton.elim _ _ }

/-- 概要：π_* 同型である Kan fibration の非空な fiber の終対象射は全単射 RLP を持つ。
方針：長完全列からの全基点の消滅を幾何的な境界充填へ戻す。
規約：fiber の頂点 v を明示する。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。acyclic fibration の相対充填。 -/
theorem fiber_terminal_rlp_of_piIsomorphism {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (b : B _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) _⦋0⦌) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.terminal_rlp_of_homotopySubsingleton v (fun w n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopySubsingleton_at p hp b w n)

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exists_boundary_filler_of_homotopySubsingleton := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_boundary_filler_of_homotopySubsingleton

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.fiber_terminal_rlp_of_piIsomorphism := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_terminal_rlp_of_piIsomorphism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.terminal_rlp_of_homotopySubsingleton := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.terminal_rlp_of_homotopySubsingleton
