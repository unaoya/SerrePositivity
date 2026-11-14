module
public import SerrePositivity.KST.SConstruction.StableArrowLoopEndpointRepresentative
public import SerrePositivity.KST.SConstruction.StableZeroIntervalLoop
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：零完全関手の区間自己比較は、両端の類が恒等なら恒等の類に一致する。
方針：両端固定の代表を固定端点区間 Hom へ戻し、同じ零成分の一意性を適用する。
規約：元の辺・元の全自己比較の類を保持。追加の自然収縮は仮定しない。
使われ方：恒等実右面の上下全比較の共有対角を同じ類へ合わせる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma endpointPairEdgeVertex {X : SSet.{u}} {x y : X _⦋0⦌} (F : SSet.Edge x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)) = (x, y) := by
  apply Prod.ext
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)) = x
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    have h : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)) := by
      apply stdSimplex.obj₀Equiv.injective
      rfl
    rw [h, ← SSet.yonedaEquiv_comp, F.δ_one_yonedaEquiv_symm]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv x
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)) = y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    have h : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
        SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)) := by
      apply stdSimplex.obj₀Equiv.injective
      rfl
    rw [h, ← SSet.yonedaEquiv_comp, F.δ_zero_yonedaEquiv_symm]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv y

private lemma fixedEndpointLoop_lift {X : SSet.{u}} {x y : X _⦋0⦌}
    (F : SSet.Edge x y)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)))
    (he : (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X))).edge =
      (SSet.Truncated.Edge.id ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)))).edge) :
    ∃ w : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge F),
      (w.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y))))).edge = e.edge := by
  let U : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X := SSet.yonedaEquiv.symm e.edge
  have hp := he
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X).app (Opposite.op ⦋1⦌) e.edge = _ at hp
  rw [endpointPairEdgeVertex F] at hp
  have h₀ : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.const x := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X).app (Opposite.op ⦋1⦌) e.edge).1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1
    exact (congrArg Prod.fst hp).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x).symm
  have h₁ : U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.const y := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair X).app (Opposite.op ⦋1⦌) e.edge).2 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1
    exact (congrArg Prod.snd hp).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one y).symm
  have hh₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ uncurry U = SSet.const x := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact h₀
  have hh₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ uncurry U = SSet.const y := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact h₁
  let γ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (uncurry U) hh₀ hh₁
  have hγ : γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) = U := by
    apply uncurry_injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry γ = uncurry U
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints (uncurry U) hh₀ hh₁
  have hv : (SSet.yonedaEquiv γ).val = e.edge := by
    have h := SSet.yonedaEquiv_comp γ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)))
    have hu : SSet.yonedaEquiv U = e.edge :=
      Equiv.apply_symm_apply (SSet.yonedaEquiv
        (X := (ihom (Δ[1] : SSet.{u})).obj X) (n := ⦋1⦌))
        (show ((ihom (Δ[1] : SSet.{u})).obj X) _⦋1⦌ from e.edge)
    exact h.symm.trans ((congrArg SSet.yonedaEquiv hγ).trans hu)
  let w : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge F) := {
    edge := SSet.yonedaEquiv γ
    src_eq := by
      apply Subtype.ext
      change ((ihom (Δ[1] : SSet.{u})).obj X).map (SimplexCategory.δ (1 : Fin 2)).op
        (SSet.yonedaEquiv γ).val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)
      rw [hv]
      exact e.src_eq
    tgt_eq := by
      apply Subtype.ext
      change ((ihom (Δ[1] : SSet.{u})).obj X).map (SimplexCategory.δ (0 : Fin 2)).op
        (SSet.yonedaEquiv γ).val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm F.edge)
      rw [hv]
      exact e.tgt_eq }
  exact ⟨w, hv⟩

/-- 概要：零完全関手の両端で恒等な区間自己比較は恒等の類となる。
方針：同じ類の両端固定代表を区間 Hom に戻し、零成分の一意性を使う。
規約：元の全自己比較の類。使われ方：上下全比較の共有対角の一致。 -/
lemma stableZeroArrowLoop_homMk_eq_id (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x))
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).edge)))
    (h₀ : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    (h₁ : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _)) :
    SSet.Truncated.HomotopyCategory.homMk e =
      SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _) := by
  obtain ⟨e', hp, hc⟩ := stableArrowLoop_endpointRepresentative_exists _ e h₀ h₁
  obtain ⟨w, hw⟩ := fixedEndpointLoop_lift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F) e' hp
  have he := stableZeroInterval_hom_ext A B F hF
    (SSet.Truncated.HomotopyCategory.homMk w)
    (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  let j : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex B) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex B)))
  have hm := congrArg ((hoFunctor.map j).toFunctor.map) he
  change SSet.Truncated.HomotopyCategory.homMk (w.map ((truncation 2).map j)) =
    SSet.Truncated.HomotopyCategory.homMk
      ((SSet.Truncated.Edge.id _).map ((truncation 2).map j)) at hm
  have hwe : w.map ((truncation 2).map j) = e' := by
    apply SSet.Truncated.Edge.ext
    exact hw
  have hm' := hm.trans (congrArg SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F))
      ((truncation 2).map j)))
  have hh : SSet.Truncated.HomotopyCategory.homMk e' =
      SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _) := by
    exact (congrArg SSet.Truncated.HomotopyCategory.homMk hwe).symm.trans hm'
  exact hc.symm.trans hh
end SerrePositivity.KST.SConstruction
