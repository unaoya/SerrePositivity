module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTransportSquareFiberComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Transport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection
/-!
概要：同じ実四角形の fiber 射を、対象宇宙持ち上げ後の同じ実 fiber 射へ比較する。
方針：元の fiber 同型で全単体を照合し、同じ射の同値性を移す。
規約：元の実四角形を変えない。使われ方：Hom の生の fiber から pointed 表示への接続。
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
/-- 同じ実四角形の fiber 射の持ち上げは、標準 fiber 同型と厳密に可換。 -/
lemma dgTransportSquareFiberMap_ulift {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} q (g.app _ b)).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap ((SSet.uliftFunctor.{v, u}).map p)
        ((SSet.uliftFunctor.{v, u}).map q) ((SSet.uliftFunctor.{v, u}).map f)
        ((SSet.uliftFunctor.{v, u}).map g)
        (by rw [← Functor.map_comp, h, Functor.map_comp]) (ULift.up b) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨t⟩
  apply Subtype.ext
  rfl
/-- 元の実 fiber 射の同値性は、同じ実四角形の宇宙持ち上げ後にも保たれる。 -/
lemma dgTransportSquareFiberMap_ulift_isQCatEquivalence {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (b : B _⦋0⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap ((SSet.uliftFunctor.{v, u}).map p)
      ((SSet.uliftFunctor.{v, u}).map q) ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g)
      (by rw [← Functor.map_comp, h, Functor.map_comp]) (ULift.up b)) := by
  have hu := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b)).mpr he
  have H := hu.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} q (g.app _ b))).isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} q (g.app _ b)).hom) at H
  rw [dgTransportSquareFiberMap_ulift] at H
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} p b)).isQCatEquivalence.cancel_left H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
