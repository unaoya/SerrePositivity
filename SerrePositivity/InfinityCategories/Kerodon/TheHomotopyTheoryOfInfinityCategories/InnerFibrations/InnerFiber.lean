module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
概要：inner fibration の頂点上の fiber の quasicategory 性。
方針：fiber の内ホーンを標的の定値単体の上で持ち上げる。
規約：射の始域・標的の quasicategory 性は不要。
使われ方：Kerodon §4.1.4（Tag 01BS）、§4.6.6（Tag 04HY） の関手単体集合の fiber。

対応節は Kerodon 4.1（Tag 01B8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-- 概要：inner fibration の各頂点上の fiber は quasicategory。
方針：内ホーンの射を元の始域へ含め、定値の標的の上で充填する。
規約：元の二つの単体集合には quasicategory 性を仮定しない。
使われ方：Kerodon §4.1.4（Tag 01BS）、§4.6.6（Tag 04HY） の fiber の圏構造。 -/
instance innerFibration_vertexFiber_quasicategory {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] (b : B _⦋0⦌) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) where
  hornFilling' {n i} a h₀ hlast := by
    have := InnerFibration.mem (q := p) _ (innerHornInclusions.intro i h₀ hlast)
    have hw : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) ≫ p = (horn (n + 2) i).ι ≫ SSet.const b := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    let sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (horn (n + 2) i).ι p (SSet.const b) := ⟨hw⟩
    let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b sq.lift sq.fac_right
    refine ⟨F, ?_⟩
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact sq.fac_left.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations
