module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiniteMappingCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility

/-! # 終対象への有限写像錐

概要：任意の図式を終対象の方向へ収縮し、写像円柱型の錐全体へ延長する。
方針：定値終対象関手の終対象性から実ホモトピーを取り、終端を一点へ貼る。
規約：始点の指定図式を厳密に保持する。使われ方：有限対充填による slice 引き戻しの収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 一点への定値射は有限写像錐の貼り合わせ射になる。 -/
def finiteConeMap (K : SSet.{u}) : K ⟶ (Δ[0] : SSet.{u}) :=
  SSet.const (stdSimplex.obj₀Equiv.symm 0)

/-- 任意の図式は終対象の方向の写像錐へ延長できる。 -/
lemma IsTerminalVertex.finiteCone_extension {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) {K : SSet.{u}} (b : K ⟶ X) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder (finiteConeMap K) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource (finiteConeMap K) ≫ G = b := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : K ⟶ X)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _ (fun _ => by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact hx)
  obtain ⟨e⟩ := ht.nonempty_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
  let G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder (finiteConeMap K) ⟶ X :=
    pushout.desc ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) (SSet.const x) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, H.h₁, SSet.comp_const])
  refine ⟨G, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ pushout.inl _ _) ≫ G = b
  rw [Category.assoc, pushout.inl_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
  exact H.h₀

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsTerminalVertex (finiteCone_extension)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
