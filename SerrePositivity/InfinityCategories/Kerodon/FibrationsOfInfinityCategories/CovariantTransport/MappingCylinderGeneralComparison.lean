module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderQuasicategoryComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.InnerAnodynePrismExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の単体集合の関手の写像円柱の区間上の比較。
方針：両端 fiber 上で因子を quasicategory に置換し、prism を延長して既存の判定を適用する。
規約：因子の quasicategory 性と構造射の単射性は仮定しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、有限 scaffold の全空間の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：写像円柱上の比較は両端の同値と垂直辺の cocartesian 性から前合成同値になる。
方針：内ホーンの置換で両因子を充填可能にし、両端固定の prism の延長と円柱の同値で元へ戻す。
規約：標的 E のみ quasicategory、因子 X・Y と射 f は任意。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N） の区間上の写像円柱の判定。 -/
@[kerodon 024P]
lemma mappingCylinder_isPrecompositionEquivalence
    {X Y E : SSet.{u}} [Quasicategory E]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (_hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (z0 : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z0) (he1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex H x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pushout.desc H g w) := by
  obtain ⟨X', a, q0, ha, hX', hq0, hfac0⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_quasicategory_resolution_over z0
  obtain ⟨Y', b, q1, hb, hY', hq1, hfac1⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_quasicategory_resolution_over z1
  have : Quasicategory X' := hX'
  have : Quasicategory Y' := hY'
  have := ha (terminal.from Y') (InnerFibration.mem (q := terminal.from Y'))
  let sq : CommSq (f ≫ b) a (terminal.from Y') (terminal.from X') := ⟨terminal.hom_ext _ _⟩
  let f' : X' ⟶ Y' := sq.lift
  have hab : f ≫ b = a ≫ f' := sq.fac_left.symm
  let F0 := q0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let g' := q1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have hgg : b ≫ g' = g := by
    change b ≫ q1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _ = g
    rw [← Category.assoc, hfac1, hz1]
  have h0 : a ≫ F0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H := by
    change a ≫ q0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _ = _
    rw [← Category.assoc, hfac0, hz0]
  have h1 : a ≫ (f' ≫ g') = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H := by
    rw [← Category.assoc, ← hab, Category.assoc, hgg]
    exact w.symm
  have h0p : F0 ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simp only [F0, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have hgp : g' ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    simp only [g', Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have h1p : (f' ≫ g') ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [Category.assoc, hgp, SSet.comp_const]
  obtain ⟨K, hK, hK0, hK1, hKp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerAnodyne_extend_prism_over_interval a ha p H hH
    F0 (f' ≫ g') h0 h1 h0p h1p
  have hae := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne a ha
  have hbe := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne b hb
  have hq0e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence q0 := by
    apply hae.cancel_left
    rwa [hfac0]
  have hq1e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence q1 := by
    apply hbe.cancel_left
    rwa [hfac1]
  have hKc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerAnodyne_prism_vertical_isCocartesian a ha p H K hK hc
  have hnew := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinder_isPrecompositionEquivalence_of_quasicategory_factors f' p K g'
    hK1 hKp hgp q0 hK0.symm q1 rfl hq0e hq1e hKc
  have hmap := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderMap_isPrecompositionEquivalence f f' a b hab hae hbe
  have hcmp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderMap_desc f f' a b hab H g K g' w hK1 hK hgg
  have h := hmap.comp hnew
  rwa [hcmp] at h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
