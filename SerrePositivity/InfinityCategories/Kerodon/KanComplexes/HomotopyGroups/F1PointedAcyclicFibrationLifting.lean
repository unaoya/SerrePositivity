module


public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
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
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.AcyclicKanLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationIntervalLifting

/-!
分割で生成：docstring を書き直すこと
概要：π_* 同型である非空な Kan fibration の全単射 RLP。
方針：底の単体を頂点へ収縮し、fiber の充填を相対区間充填で元の正方形へ戻す。
規約：源の非空性を参照頂点で指定する。HT-KQ は使わない。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）、BF 1978 §2。Whitehead の充填による証明。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全ての fiber が全単射 RLP を持つ Kan fibration は任意の境界正方形を充填する。
方針：底の標準単体の収縮を境界で持ち上げ、終点の fiber 内で充填して始点へ戻す。
規約：全空間や底の Kan 性はこの相対補題には不要。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。acyclic fibration の境界 RLP。 -/
theorem exists_boundary_lift_of_fiber_lifting {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p]
    (hF : ∀ b : B _⦋0⦌,
      (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b)))
    (n : ℕ) (a : (boundary.{u} n : SSet.{u}) ⟶ E) (b : (Δ[n] : SSet.{u}) ⟶ B)
    (hab : a ≫ p = (boundary n).ι ≫ b) :
    ∃ t : (Δ[n] : SSet.{u}) ⟶ E, (boundary n).ι ≫ t = a ∧ t ≫ p = b := by
  let i := (boundary.{u} n).ι
  let x := b.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.vertex n)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.map.{u} n ≫ b
  have hq₀ : SSet.ι₀ ≫ q = b := by
    dsimp only [q]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.zero, Category.id_comp]
  have hq₁ : SSet.ι₁ ≫ q = SSet.const x := by
    dsimp only [q]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction.one, SSet.const_comp]
  let qA := i ▷ (Δ[1] : SSet.{u}) ≫ q
  have ha : a ≫ p = SSet.ι₀ ≫ qA := by
    dsimp only [qA]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, hq₀]
    exact hab
  obtain ⟨l, hl₀, hlp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_fibration_interval_lift p a qA ha
  let a₁ := SSet.ι₁ ≫ l
  have ha₁ : a₁ ≫ p = SSet.const x := by
    dsimp only [a₁]
    rw [Category.assoc, hlp]
    dsimp only [qA]
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, hq₁, SSet.comp_const]
  let aF := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p x a₁ ha₁
  let : HasLiftingProperty i (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p x)) := hF x i inferInstance
  let sqF : CommSq aF i (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p x)) (terminal.from (Δ[n] : SSet.{u})) :=
    ⟨Subsingleton.elim _ _⟩
  let s := sqF.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p x
  have hs : i ≫ s = a₁ := by
    dsimp only [s]
    rw [← Category.assoc, sqF.fac_left, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
  have hsp : s ≫ p = SSet.const x := by
    dsimp only [s]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, SSet.comp_const]
  let H : SSet.Homotopy a (i ≫ s) := {
    h := l
    h₀ := hl₀
    h₁ := hs.symm
    rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
  have hp : J.rlp p := (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  obtain ⟨t, ht, V, _hV, hVp⟩ := KanFibrationEndpointExtension.exists_from_one
    p hp i s a H q (hsp.trans hq₁.symm) hlp
  refine ⟨t, ht, ?_⟩
  calc
    t ≫ p = (SSet.ι₀ ≫ V.h) ≫ p := by rw [V.h₀]
    _ = SSet.ι₀ ≫ q := by rw [Category.assoc, hVp]
    _ = b := hq₀

/-- 概要：全ての fiber の終対象射が全単射 RLP を持つ Kan fibration 自身も全単射 RLP。
方針：相対境界充填を単射の境界 cell 分解へ拡張する。
規約：RLP の閉性以外のモデル構造の公理を使わない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。実際の持ち上げによる弱同値の検出。 -/
theorem fibration_rlp_of_fiber_lifting {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hF : ∀ b : B _⦋0⦌,
      (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b))) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
  rw [SSet.rlp_monomorphisms]
  intro A B i hi
  rcases hi with ⟨n⟩
  constructor
  intro a b sq
  obtain ⟨t, ht, htp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_boundary_lift_of_fiber_lifting p hF n a b sq.w
  exact CommSq.HasLift.mk' { l := t, fac_left := ht, fac_right := htp }

/-- 概要：非空な Kan 複体間の π_* 同型である Kan fibration は全単射 RLP を持つ。
方針：零次数から各 fiber の頂点を選び、全次数の消滅から fiber の充填性を導く。
規約：全空間の参照頂点 e₀ を明示する。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）、BF 1978 §2。Whitehead の相対版。 -/
theorem fibration_rlp_of_piIsomorphism {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (e₀ : E _⦋0⦌) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_fiber_lifting p
  intro b
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_surjective_vertices_of_piIsomorphism p hp e₀ b
  subst b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_terminal_rlp_of_piIsomorphism p hp (p.app _ e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
