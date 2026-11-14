module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeLeftFibrationPrism

/-!
概要：部分図式の輸送を固定して、全図式を指定した終点 fiber へ輸送する。
方針：部分円柱と始点を保つ prism の持ち上げの終点を fiber に制限する。
規約：底の全円柱も部分図式の全円柱も厳密に保持する。
使われ方：一般 coherent な filtered 図式の境界固定の有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：部分図式の指定輸送を保つ、全図式の終点 fiber への輸送。
方針：相対 prism を持ち上げ、終点とその制限を計算する。
規約：底や形状の充填性・有限性は不要。使われ方：境界固定の fiber 検出。 -/
lemma leftFibration_transport_to_fiber_relative {A K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : A ⟶ K) [Mono i] (f : K ⟶ E)
    (b : B _⦋0⦌) (h : SSet.Homotopy (f ≫ p) (SSet.const b))
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (H : SSet.Homotopy (i ≫ f) (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))
    (hHp : H.h ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ h.h) :
    ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b, i ≫ g = a ∧
      ∃ G : SSet.Homotopy f (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = H.h ∧ G.h ≫ p = h.h := by
  let t := (β_ (Δ[1] : SSet.{u}) K).hom ≫ h.h
  let s := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h
  have ht : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ t := by
    dsimp only [t]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact h.h₀.symm
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ s = i ≫ f := by
    dsimp only [s]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact H.h₀
  have hsp : s ≫ p = (Δ[1] ◁ i) ≫ t := by
    dsimp only [s, t]
    rw [Category.assoc, hHp, ← Category.assoc,
      ← BraidedCategory.braiding_naturality_right, Category.assoc]
  obtain ⟨L, hL₀, hLs, hLp⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.leftFibration_lift_prism_relative p i f t s ht hs hsp
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  have hR₀ : SSet.ι₀ ≫ R = f := by
    dsimp only [R]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding K, Category.assoc, ← Category.assoc
      (β_ (Δ[1] : SSet.{u}) K).hom, SymmetricCategory.symmetry, Category.id_comp]
    exact hL₀
  have hRp : R ≫ p = h.h := by
    dsimp only [R]
    rw [Category.assoc, hLp]
    dsimp only [t]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hRi : (i ▷ (Δ[1] : SSet.{u})) ≫ R = H.h := by
    dsimp only [R]
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc, hLs]
    dsimp only [s]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have he : (SSet.ι₁ ≫ R) ≫ p = SSet.const b := by
    rw [Category.assoc, hRp]
    exact h.h₁
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (SSet.ι₁ ≫ R) he
  refine ⟨g, ?_, ⟨R, hR₀, rfl, ?_⟩, hRi, hRp⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    change i ≫ SSet.ι₁ ≫ R = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hRi, H.h₁]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
