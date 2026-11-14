module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity

/-!
概要：filtered な底の left fibration の有限図式を一つの fiber へ輸送する。
方針：底の余錐の指定収縮を始点固定で持ち上げ、終点を fiber に入れる。
規約：底は通常の圏の nerve に限定せず、指定した底の円柱全体を保持する。
使われ方：一般 coherent な空間値図式の全空間の有限パラメータの検出。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：底で指定した余錐に沿い、全空間の図式をその頂点 fiber へ輸送する。
方針：left fibration の prism の持ち上げの終点を fiber に制限する。
規約：始点・底の全円柱を厳密に保持する。使われ方：有限図式の fiber への移動。 -/
lemma leftFibration_transport_to_cocone_fiber {K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : K ⟶ E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ p)) :
    ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c.vertex,
      ∃ H : SSet.Homotopy f (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c.vertex),
        H.h ≫ p = (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeNullHomotopy c).h := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeNullHomotopy c
  let b := (β_ (Δ[1] : SSet.{u}) K).hom ≫ h.h
  have hb : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ b := by
    dsimp only [b]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact h.h₀.symm
  obtain ⟨L, hL₀, hLp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_lift_prism p f b hb
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  have hR₀ : SSet.ι₀ ≫ R = f := by
    dsimp only [R]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding K, Category.assoc, ← Category.assoc
      (β_ (Δ[1] : SSet.{u}) K).hom, SymmetricCategory.symmetry, Category.id_comp]
    exact hL₀
  have hRp : R ≫ p = h.h := by
    dsimp only [R]
    rw [Category.assoc, hLp]
    dsimp only [b]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have ht : (SSet.ι₁ ≫ R) ≫ p = SSet.const c.vertex := by
    rw [Category.assoc, hRp]
    exact h.h₁
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p c.vertex (SSet.ι₁ ≫ R) ht
  refine ⟨g, ⟨R, hR₀, rfl, ?_⟩, hRp⟩
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact False.elim x.1.property

/-- 概要：filtered な底の全空間への有限射は一つの fiber を経由する射にホモトピック。
方針：底の有限図式の余錐を選び、その指定収縮を持ち上げる。
規約：任意の left fibration と有限単体集合。使われ方：coherent な filtered 余極限の検出。 -/
lemma leftFibration_finite_fiber_detection {K E B : SSet.{u}}
    [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : K ⟶ E) :
    ∃ b : B _⦋0⦌, ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b,
      Nonempty (SSet.Homotopy f (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) := by
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty (f ≫ p)
  obtain ⟨g, H, _⟩ := leftFibration_transport_to_cocone_fiber p f c
  exact ⟨c.vertex, g, ⟨H⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
