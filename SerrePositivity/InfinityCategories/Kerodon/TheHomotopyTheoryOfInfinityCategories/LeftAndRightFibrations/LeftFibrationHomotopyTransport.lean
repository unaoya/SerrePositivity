module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath

/-!
概要：底で指定した定値終点への任意のホモトピーに沿い、全図式を一つの fiber へ輸送する。
方針：指定した円柱全体を始点固定で持ち上げ、その終点を fiber に入れる。
規約：底の全円柱を厳密に保持する。
使われ方：複数の有限図式を同じ filtered な底の頂点へ同時に輸送する。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：指定した底の収縮に沿う全空間図式の終点 fiber への輸送。
方針：区間を左に並べ替え、left fibration の始点固定 prism を持ち上げる。
規約：指定した底の全円柱を保つ。使われ方：同時の有限図式の輸送。 -/
lemma leftFibration_transport_along_nullHomotopy {K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : K ⟶ E) (b : B _⦋0⦌)
    (h : SSet.Homotopy (f ≫ p) (SSet.const b)) :
    ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b, ∃ H : SSet.Homotopy f (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b),
      H.h ≫ p = h.h := by
  let t := (β_ (Δ[1] : SSet.{u}) K).hom ≫ h.h
  have ht : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ t := by
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ t = SSet.ι₀ ≫ h.h from rfl, h.h₀]
  obtain ⟨L, hL₀, hLp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_lift_prism p f t ht
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  have hR₀ : SSet.ι₀ ≫ R = f := by
    rw [show SSet.ι₀ ≫ R = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L from rfl, hL₀]
  have hRp : R ≫ p = h.h := by
    dsimp only [R, t] at *
    rw [Category.assoc, hLp, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hR₁ : (SSet.ι₁ ≫ R) ≫ p = SSet.const b := by
    rw [Category.assoc, hRp, h.h₁]
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (SSet.ι₁ ≫ R) hR₁
  refine ⟨g, ⟨R, hR₀, ?_, ?_⟩, hRp⟩
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p b _ hR₁).symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
