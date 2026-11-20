module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.Unique
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction

/-!
概要：Kan 複体へ向かう境界射を最後のホーン上で定数となる射へ正規化する。
方針：ホーンの収縮を境界全体へ区間の端点充填で延長する。
規約：変更前後の実際のホモトピーを保持する。π_* の消滅はこの工程に不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。ホモトピー類の消滅からの境界充填。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.BoundaryNormalization
end SerrePositivity.KST.Spectra.BoundaryNormalization
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.BoundaryNormalization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：ホーンは同じ次元の境界に含まれる。
方針：最後以外の面の supremum を全ての面の supremum へ含める。
規約：任意のホーンの添字。
使われ方：Goerss–Jardine I §7。正規化する部分複体の包含。 -/
theorem horn_le_boundary (n : ℕ) (j : Fin (n + 1)) : horn.{u} n j ≤ boundary n := by
  rw [horn_eq_iSup]
  exact iSup_le (fun k ↦ face_singleton_compl_le_boundary k.val)

/-- 概要：最後のホーンから同次元の境界への包含。
方針：部分複体の包含の射を使う。
規約：次元 n+1 は正。
使われ方：Goerss–Jardine I §7。ホモトピー延長の左辺。 -/
def inclusion (n : ℕ) : (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u}) ⟶
    (boundary.{u} (n + 1) : SSet.{u}) :=
  Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.horn_le_boundary (n + 1) (Fin.last (n + 1)))

/-- 概要：ホーンから境界への包含は単射。
方針：部分複体の包含の単射性を使う。
規約：基礎単体集合の Mono。
使われ方：Goerss–Jardine I §7。区間の端点の相対充填。 -/
instance inclusion_mono (n : ℕ) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion.{u} n) :=
  inferInstanceAs (Mono (Subcomplex.homOfLE
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.horn_le_boundary (n + 1) (Fin.last (n + 1)))))

/-- 概要：ホーンから境界への包含を標準単体へ含めると元のホーン包含。
方針：部分複体の包含の定義を比較する。
規約：点つき条件は不要。
使われ方：Goerss–Jardine I §7。面の包含の比較。 -/
@[reassoc (attr := simp)]
theorem inclusion_ι (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion.{u} n ≫ (boundary (n + 1)).ι =
    (horn (n + 1) (Fin.last (n + 1))).ι := rfl

/-- 概要：最後以外の面はホーンから境界への包含を通る。
方針：標準単体への包含の単射性で二つの面の射を比較する。
規約：j は最後の面でない。
使われ方：Goerss–Jardine I §7。正規化した境界の各面の値。 -/
@[reassoc]
theorem hornFace_inclusion (n : ℕ) (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    horn.ι (Fin.last (n + 1)) j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion.{u} n = boundary.ι j := by
  apply (cancel_mono (boundary (n + 1)).ι).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion_ι, horn.ι_ι, boundary.ι_ι]

/-- 概要：ホーン上で定数の境界射は最後以外の全ての面で同じ定数値。
方針：ホーンを通る各面の表示へ正規化条件を適用する。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7。PtSimplex の境界条件の検証。 -/
theorem normalized_face {X : SSet.{u}} (n : ℕ) (x : X _⦋0⦌)
    (g : (boundary.{u} (n + 1) : SSet.{u}) ⟶ X)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion n ≫ g = SSet.const x) (j : Fin (n + 2))
    (hj : j ≠ Fin.last (n + 1)) : boundary.ι j ≫ g = SSet.const x := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.hornFace_inclusion n j hj, Category.assoc, hg, SSet.comp_const]

/-- 概要：任意の Kan 値の境界射は最後のホーン上で定数となる境界射へホモトピック。
方針：ホーンの収縮を後合成し、区間の始点を保つ延長を境界全体へ行う。
規約：境界の次元は n+1。得られる基点 x は境界の最後の頂点の像。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。境界の代表を PtSimplex へ直す。 -/
theorem exists_normalization {X : SSet.{u}} [KanComplex X] (n : ℕ)
    (f : (boundary.{u} (n + 1) : SSet.{u}) ⟶ X) :
    ∃ (x : X _⦋0⦌) (g : (boundary.{u} (n + 1) : SSet.{u}) ⟶ X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion n ≫ g = SSet.const x ∧ Nonempty (SSet.Homotopy f g) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.inclusion.{u} n
  let x := (i ≫ f).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.vertex n)
  let H : SSet.Homotopy (i ≫ f) (SSet.const x) := by
    simpa only [Category.id_comp, SSet.const_comp] using
      HomotopyClasses.postHomotopy (i ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction.homotopy n)
  have hX : J.rlp (terminal.from X) := (fibration_iff _).1 inferInstance
  obtain ⟨g, hg, V, _hV, _hVp⟩ := KanFibrationEndpointExtension.exists_from_zero
    (terminal.from X) hX i f (SSet.const x) H (terminal.from _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact ⟨x, g, hg, ⟨V⟩⟩

/-- 概要：ホモトピックな境界射のうち終点が充填可能なら始点も充填可能。
方針：境界包含に沿う区間の終点を保つ延長を使う。
規約：Kan 値の任意の境界次元。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。正規化した境界の充填を元へ戻す。 -/
theorem exists_filler_of_homotopy {X : SSet.{u}} [KanComplex X] (n : ℕ)
    (f g : (boundary.{u} n : SSet.{u}) ⟶ X) (H : SSet.Homotopy f g)
    (s : (Δ[n] : SSet.{u}) ⟶ X) (hs : (boundary n).ι ≫ s = g) :
    ∃ t : (Δ[n] : SSet.{u}) ⟶ X, (boundary n).ι ≫ t = f := by
  let H' : SSet.Homotopy f ((boundary n).ι ≫ s) := by
    rw [hs]
    exact H
  have hX : J.rlp (terminal.from X) := (fibration_iff _).1 inferInstance
  obtain ⟨t, ht, _V⟩ := KanFibrationEndpointExtension.exists_from_one
    (terminal.from X) hX (boundary n).ι s f H' (terminal.from _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact ⟨t, ht⟩

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
