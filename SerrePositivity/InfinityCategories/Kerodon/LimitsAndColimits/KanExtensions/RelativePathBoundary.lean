module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetPathVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismFinalBoundary

/-!
概要：inner fibration と可逆辺の持ち上げから相対可逆 path の全境界を充填する。
方針：零次元は可逆辺の持ち上げ、正次元は終点固定の相対 prism の延長を使う。
規約：像と終点は厳密に固定する。
使われ方：相対内部 Hom の同値の持ち上げと指定部分固定の厳密化。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：inner fibration で可逆辺を終点指定で持ち上げられれば相対 path 比較は自明 Kan。
方針：境界上の可逆 path と終点を相対 prism として延長し、全部分複体へ戻す。
規約：元と標的は quasicategory、可逆辺の持ち上げは指定された辺自体を保つ。
使われ方：isofibration の操作的条件から同値の族の境界固定の持ち上げを得る。 -/
lemma kanRelativeEquivalencePathMapAt_one_trivialKanFibration
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let v := b ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1) p
  let f := b ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1) p
  have hvf : v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = f ≫ p := by
    dsimp [v, f]
    rw [Category.assoc, pullback.condition, Category.assoc]
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p = (boundary n).ι ≫ v := by
    have h := congrArg (fun k ↦ k ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1) p) sq.w
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst, v] using h
  have hf : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 = (boundary n).ι ≫ f := by
    have h := congrArg (fun k ↦ k ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1) p) sq.w
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd, f] using h
  cases n with
  | zero =>
    have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv v) = p.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv f) := by
      simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv hvf
    obtain ⟨w, hwp, hwt⟩ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanEquivalencePathVertex_lift_of_targetLifting p hp (SSet.yonedaEquiv f) _ hv
    refine CommSq.HasLift.mk' { l := SSet.yonedaEquiv.symm w, fac_left := ?_, fac_right := ?_ }
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro x
      have hx := x.property
      generalize x.val = z at hx
      rw [boundary_zero] at hx
      exact False.elim hx
    · apply pullback.hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst]
        change SSet.yonedaEquiv.symm w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p = v
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
        exact hwp
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd]
        change SSet.yonedaEquiv.symm w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 = f
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
        exact hwt
  | succ n =>
    let H := uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E)
    let β := uncurry (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B)
    have hC : curry H = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E := curry_uncurry _
    have hF : (boundary (n + 1)).ι ≫ f =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
      exact hf.symm
    have hHp : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ β := by
      have he : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E) ≫ (ihom (Δ[1] : SSet.{u})).map p =
          (boundary (n + 1)).ι ≫ (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B) := by
        rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc, ha, Category.assoc]
      have h := congrArg uncurry he
      rw [uncurry_natural_right, uncurry_natural_left] at h
      exact h
    have hfp : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n + 1] : SSet.{u}) ≫ β := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
      exact hvf.symm
    have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismBoundaryLastVerticalEdge n))) := by
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E).app (Opposite.op ⦋0⦌) _) at hx
      rw [← hC, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hx
      exact hx
    obtain ⟨F, hF, hF₁, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prism_lift_boundary_with_final_endpoint p n H f β hF hHp hfp hH
    have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E := by
      rw [← curry_natural_left, hF, hC]
    have hv : ∀ x : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((curry F).app (Opposite.op ⦋0⦌) x) := by
      intro x
      let y : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨x, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv x)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) y)
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) y
      change (curry F).app (Opposite.op ⦋0⦌) x =
        (a.app (Opposite.op ⦋0⦌) y).val at he
      exact he.symm ▸ hx
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (curry F) hv
    have hg : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E = curry F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
      apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E)).1
      rw [Category.assoc, hg, hc]
    · apply pullback.hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst]
        have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
        apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B)).1
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc, hg]
        apply uncurry_injective
        rw [uncurry_natural_right, uncurry_curry, hFp]
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd]
        change g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = f
        rw [← Category.assoc, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₁]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
