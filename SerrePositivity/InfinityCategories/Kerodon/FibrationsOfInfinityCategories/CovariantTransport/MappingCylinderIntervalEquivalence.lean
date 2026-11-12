module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinExtensionEquivalence

/-!
概要：quasicategory の単射な関手の写像円柱の区間上の比較。
方針：円柱上の比較を相対 join へ延長し、両端と垂直辺の条件による同値判定を適用する。
規約：ここでは因子の quasicategory 性と構造射の単射性を仮定する。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、有限 scaffold の全空間比較への準備。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：単射な関手の写像円柱上の比較は、両端の同値と垂直辺の cocartesian 性で前合成同値になる。
方針：相対 join への厳密な延長を取り、その同値と円柱比較の前合成同値を合成する。
規約：X・Y・E は quasicategory、f は単射。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N） の quasicategory の因子かつ単射の場合。 -/
lemma mappingCylinder_isPrecompositionEquivalence_of_quasicategories
    {X Y E : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    (f : X ⟶ Y) [Mono f] (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (z0 : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z0) (he1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex H x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pushout.desc H g w) := by
  obtain ⟨G, hGH, hGg, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_of_prism_over_interval f p H g w hH hg
  have hG := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_isQCatEquivalence f p G hGp H hGH g hGg
    z0 hz0 z1 hz1 he0 he1 hc
  have hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f ≫ G = pushout.desc H g w := by
    apply pushout.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl, hGH, pushout.inl_desc]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr, hGg, pushout.inr_desc]
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison f).comp
    hG.isPrecompositionEquivalence
  rwa [hcomp] at h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
