module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：最後の頂点が終対象である prism の、境界と両端を固定した延長。
方針：二端点と単体の境界を貼り、新しいセルの最後の頂点を (1,last) に同定する。
規約：他の頂点の終対象性は要求しない。使われ方：lax pullback の相対終点境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma terminal_prism_extend_two_endpoints {X : SSet.{u}} (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ X)
    (F₀ F₁ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (h₀ : (boundary (n + 1)).ι ≫ F₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H)
    (h₁ : (boundary (n + 1)).ι ≫ F₁ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F₁.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ X,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ F = F₀ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ F = F₁ := by
  let S := boundary.{u} 1
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F₀ F₁ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, h₀, h₁]
  let a := q.desc H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F₀ F₁) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F₀ F₁ :=
    q.inr_desc _ _ _
  let A := Subcomplex.unionProd S T
  have hA : ∀ v : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    refine Or.inl ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hterm : ∀ (m : ℕ) (s : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩) := by
    intro m s hs
    have hs₁ : s.1 ∉ S.obj (Opposite.op ⦋m + 1⦌) :=
      fun h => hs (Or.inr ⟨h, by trivial⟩)
    have hs₂ : s.2 ∉ T.obj (Opposite.op ⦋m + 1⦌) :=
      fun h => hs (Or.inl ⟨by trivial, h⟩)
    have hv₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_stdSimplex_of_notMem_boundary s.1 hs₁
    have hv₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    let w : ((S : SSet.{u}) ⊗ Δ[n + 1]) _⦋0⦌ :=
      (⟨stdSimplex.obj₀Equiv.symm 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 1⟩,
        stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app ha₂ (Opposite.op ⦋0⦌)) w
    have he : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩ =
        F₁.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_prod, hv₁, hv₂]
      change a.app (Opposite.op ⦋0⦌)
        ⟨(stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))), _⟩ = _
      change a.app (Opposite.op ⦋0⦌)
        ⟨(stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))), _⟩ =
          (if (1 : Fin 2) = 0 then F₀.app _ (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))
            else F₁.app _ (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))) at hh
      simpa using hh
    rw [he]
    exact ht
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_extension_of_terminal_last_vertices A hA a hterm
  have he : ((boundary 1).ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F₀ F₁ := by
    rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · have h := congrArg (fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 Δ[n + 1] ≫ g) he
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero] using h
  · have h := congrArg (fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 Δ[n + 1] ≫ g) he
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one] using h

end SerrePositivity.KST.LocalizingInvariants
