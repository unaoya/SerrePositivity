module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeLeftFibrationTransport

/-!
概要：共通の元の境界の輸送を、その像の有限模型の全輸送へ延長する。
方針：境界の全円柱を射で写し、相対 left fibration 輸送に指定する。
規約：元の境界円柱を選び直さない。使われ方：任意の標的二入力の境界付き同時輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の境界の輸送像を厳密に保持する、入力模型の fiber への輸送。
方針：元の境界円柱を射で写して相対輸送する。
規約：有限性不要。使われ方：二入力の模型を同じ境界輸送へ揃える。 -/
lemma leftFibration_transport_mapped_boundary {A M R E B : SSet.{u}}
    (p : R ⟶ B) (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (c : R ⟶ E) (hc : c ≫ q = p)
    (i : A ⟶ M) [Mono i] (a : A ⟶ R) (f : M ⟶ E) (hf : i ≫ f = a ≫ c)
    (b : B _⦋0⦌) (H : SSet.Homotopy (f ≫ q) (SSet.const b))
    (t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (L : SSet.Homotopy a (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))
    (hL : L.h ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    ∃ s : M ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b, i ≫ s = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b ∧
      ∃ U : SSet.Homotopy f (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ U.h = L.h ≫ c ∧ U.h ≫ q = H.h := by
  let T : SSet.Homotopy (i ≫ f)
      ((t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) :=
    { h := L.h ≫ c
      h₀ := by
        change SSet.ι₀ ≫ L.h ≫ c = i ≫ f
        rw [← Category.assoc, L.h₀, ← hf]
      h₁ := by
        change SSet.ι₁ ≫ L.h ≫ c =
          (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
        rw [← Category.assoc, L.h₁]
        simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  have hT : T.h ≫ q = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
    change (L.h ≫ c) ≫ q = _
    rw [Category.assoc, hc, hL]
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.leftFibration_transport_to_fiber_relative q i f b H
    (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q c hc b) T hT

end SerrePositivity.InfinityCategories.Project.FilteredExchange
