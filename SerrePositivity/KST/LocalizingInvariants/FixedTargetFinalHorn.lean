module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.MarkedSpanFamilyInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FinalHornRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal

/-!
概要：定値終点を持つ区間族の最終外ホーンを、指定した始点図式の上で延長する。
方針：境界図式の二変数を交換し、境界外の単体の最後の頂点での恒等辺を使う。
規約：元のホーンと両端を厳密に保持。使われ方：span の pullback 輸送の cartesian 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma interval_source_of_boundary_diagram {A X : SSet.{u}}
    (G : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (f g : A ⟶ X)
    (h : G ≫ (pre (boundary 1).ι).app X = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g)) :
    G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = f := by
  have hh := congrArg (fun k : A ⟶ (ihom (boundary 1 : SSet.{u})).obj X =>
    k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 0⟩ : (boundary 1 : SSet.{u}) _⦋0⦌)) h
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.intervalBoundaryCurry_source] at hh
  change G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = f at hh
  exact hh

lemma interval_target_of_boundary_diagram {A X : SSet.{u}}
    (G : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (f g : A ⟶ X)
    (h : G ≫ (pre (boundary 1).ι).app X = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g)) :
    G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g := by
  have hh := congrArg (fun k : A ⟶ (ihom (boundary 1 : SSet.{u})).obj X =>
    k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 1⟩ : (boundary 1 : SSet.{u}) _⦋0⦌)) h
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.intervalBoundaryCurry_target] at hh
  change G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g at hh
  exact hh

lemma exists_fixedTarget_finalHorn_extension {X : SSet.{u}} [Quasicategory X]
    (m : ℕ) (L : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶
      (ihom (Δ[1] : SSet.{u})).obj X)
    (a : (Δ[m + 2] : SSet.{u}) ⟶ X) (x : X _⦋0⦌)
    (hs : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ a)
    (ht : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const x) :
    ∃ G : (Δ[m + 2] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X,
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ G = L ∧
      G ≫ (pre (boundary 1).ι).app X = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram a (SSet.const x)) := by
  let d := curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram a (SSet.const x))
  have hL : L ≫ (pre (boundary 1).ι).app X =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ d := by
    rw [intervalFunctor_restrict_boundary, hs, ht]
    dsimp only [d]
    rw [← curry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, SSet.comp_const]
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X d
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv
    (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) (Δ[1] : SSet.{u}) X L
  have hw : A ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X =
      (boundary 1).ι ≫ B := by
    have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv
      (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) (boundary 1 : SSet.{u}) X) hL
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre] at hh
    exact hh.symm
  have hi (n : ℕ) (s : (Δ[1] : SSet.{u}) _⦋n⦌)
      (hs : s ∉ Set.range ((boundary 1).ι.app (Opposite.op ⦋n⦌))) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry B).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s) 1))) := by
    have hn : s ∉ (boundary 1).obj (Opposite.op ⦋n⦌) := by
      intro h
      exact hs ⟨⟨s, h⟩, rfl⟩
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_stdSimplex_of_notMem_boundary s hn
    have he : (uncurry B).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s) 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 := by
      rw [hv]
      dsimp [B, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m) = _
      rw [ht]
      rfl
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const x
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hx
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hx
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hx
  obtain ⟨F, hF₁, hF₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.finalHornRestriction_lift_of_last_vertices (boundary 1).ι m A B hw hi
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X).symm F
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X G = F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X).apply_symm_apply F
  refine ⟨G, ?_, ?_⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv
      (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) (Δ[1] : SSet.{u}) X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, hG]
    exact hF₂
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, hG]
    exact hF₁

end SerrePositivity.KST.LocalizingInvariants
