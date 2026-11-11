module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiberTransportSquare
/-!
概要：同じ実四角形の fiber 射は、全空間と底の写像の合成・等式に厳密に整合する。
方針：全単体の包含と fiber 射の定義を照合し、等しい四角形へ条件を移す。
規約：元の実 fiber 射を保つ。使われ方：Hom pointed 表示の全 fiber 同値の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
/-- 実四角形の fiber 射は、同じ二つの実四角形の合成を保つ。 -/
lemma dgTransportSquareFiberMap_comp {E B F D G A : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (r : G ⟶ A)
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    (f' : F ⟶ G) (g' : D ⟶ A) (h' : f' ≫ r = q ≫ g') (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p r (f ≫ f') (g ≫ g')
      (by rw [Category.assoc, h', ← Category.assoc, h, Category.assoc]) b =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap q r f' g' h' (g.app _ b) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  apply Subtype.ext
  rfl
/-- 全空間・底の写像の等式は、同じ実 fiber 射の同値条件を保つ。 -/
lemma dgTransportSquareFiberMap_congr {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f f' : E ⟶ F) (g g' : B ⟶ D)
    (hf : f = f') (hg : g = g') (h : f ≫ q = p ≫ g) (h' : f' ≫ q = p ≫ g')
    (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f' g' h' b) := by
  cases hf
  cases hg
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
