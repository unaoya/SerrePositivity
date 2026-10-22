module

public import SerrePositivity.InfinityCategories.F2.Idempotent.Retracts
public import SerrePositivity.InfinityCategories.F1B.PinchedComposition
public import SerrePositivity.InfinityCategories.F1B.ContractibleHomotopyRetract

/-!
概要：元の指定 retract に沿って、全 pinched Hom の可縮性を移す。
方針：元の前後合成の合成・恒等の全自然同型で、実際のホモトピー retract を構成する。
規約：写像空間全体を扱い、Hom の集合や π₀ の一意性だけで代用しない。
使われ方：冪等完備化に沿う始対象・終対象・零対象の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の始域が retract であるとき、元の全 pinched Hom の可縮性を戻す。 -/
lemma VertexRetraction.pinchedHom_source_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (z : X _⦋0⦌)
    (hy : IsContractibleKan (pinchedHom y z)) : IsContractibleKan (pinchedHom x z) := by
  have h := PinchedInterval.precomposeCompIso z r.i r.r
  rw [r.retract] at h
  let e := h ≪≫ PinchedInterval.precomposeIdIso x z
  exact isContractibleKan_of_homotopy_retract (PinchedInterval.precompose z r.r)
    (PinchedInterval.precompose z r.i) (FunctorIso.simplicialHomotopy e.symm) hy

/-- 元の終域が retract であるとき、元の全 pinched Hom の可縮性を戻す。 -/
lemma VertexRetraction.pinchedHom_target_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (z : X _⦋0⦌)
    (hy : IsContractibleKan (pinchedHom z y)) : IsContractibleKan (pinchedHom z x) := by
  have h := PinchedInterval.postcomposeCompIso z r.i r.r
  rw [r.retract] at h
  let e := h ≪≫ PinchedInterval.postcomposeIdIso z x
  exact isContractibleKan_of_homotopy_retract (PinchedInterval.postcompose z r.i)
    (PinchedInterval.postcompose z r.r) (FunctorIso.simplicialHomotopy e.symm) hy

end SerrePositivity.InfinityCategories.F2.Idempotent
