module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：単射への関手の制限は可逆な辺を始点を固定して持ち上げる。
方針：辺の prism を可逆ホモトピーの延長で持ち上げ、同じ一次単体へ戻す。
規約：制限先の辺そのものを厳密に保つ。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、分類図式側の一次の持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：prism 表示は関手空間への族を一意に決める。
方針：対称子を消去して uncurry の単射性を使う。
規約：全てのパラメーター空間を許す。
使われ方：Kerodon §5.6.8（Tag 02S9）、持ち上げた辺の制限の厳密な同定。 -/
lemma functorFamilyPrism_injective (K B X : SSet.{u}) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (K := K) (B := B) (X := X)) := by
  intro f g h
  apply uncurry_injective
  exact (cancel_epi (β_ K B).hom).mp h

/-- 概要：関手空間の前合成の prism は元の prism の始域制限。
方針：uncurry の前合成則と対称子の自然性を使う。
規約：制限する射に単射性を要求しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、辺の制限を prism の制限へ移す。 -/
lemma functorFamilyPrism_pre {K B D X : SSet.{u}} (F : K ⟶ (ihom B).obj X) (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (F ≫ (pre g).app X) = (K ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism, uncurry_pre_app, ← Category.assoc,
    ← BraidedCategory.braiding_naturality_right, Category.assoc]
  rfl

/-- 概要：関手の辺の prism の垂直辺は、元の辺の点での評価と同じ。
方針：prism の因子の交換を計算して、標準区間の恒等一次単体を使う。
規約：頂点の端点表示に依存しない一次単体の等式。
使われ方：Kerodon §4.5.3（Tag 032Y）、可逆ホモトピーの延長の入力。 -/
lemma functorEdgePrism_vertical {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1) =
        (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b)).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e) b).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge e b)

/-- 概要：単射への制限先の可逆な関手の辺は、指定した始点から持ち上がる。
方針：可逆な垂直辺の prism を延長し、その実際の一次単体を戻す。
規約：制限先の辺を同型な別の辺に置き換えない。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、分類図式の可逆な一次の持ち上げ。 -/
lemma pre_liftInvertibleEdge_source {B D X : SSet.{u}} [Quasicategory X]
    (g : D ⟶ B) [Mono g] (F : B ⟶ X) (G : D ⟶ X)
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    ∃ (F' : B ⟶ X) (l : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F')),
      ((pre g).app X).app (Opposite.op ⦋1⦌) l.edge = e.edge ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge l := by
  have hv : ∀ d : D _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant d 1))) := by
    intro d
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (functorEdgePrism_vertical e d)).mpr
      (he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt d))
  obtain ⟨H, hHg, hH₀, hHI⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceHomotopy_extend g (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e) F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_zero e) hv
  let F' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H
  let h : SSet.Homotopy F F' := {
    h := (β_ B (Δ[1] : SSet.{u})).hom ≫ H
    h₀ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = F; exact hH₀
    h₁ := by rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  let l := SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy h)
  have hLH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.yonedaEquiv.symm l.edge) = H := by
    change (β_ (Δ[1] : SSet.{u}) B).hom ≫
      uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry h.h))) = H
    rw [Equiv.symm_apply_apply, uncurry_curry]
    change (β_ (Δ[1] : SSet.{u}) B).hom ≫ (β_ B (Δ[1] : SSet.{u})).hom ≫ H = H
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  refine ⟨F', l, ?_, ?_⟩
  · apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_comp]
    apply functorFamilyPrism_injective (Δ[1] : SSet.{u}) D X
    rw [functorFamilyPrism_pre, hLH, hHg]
    rfl
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise h
    intro b
    have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    have hEq : H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge h b).edge := by
      change H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1) =
          H.app (Opposite.op ⦋1⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge)
      rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hEq).mp (hHI b)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
