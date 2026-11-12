module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：同じ底上の引き戻しの頂点 fiber は、元の二つの頂点 fiber の直積と同型。
方針：元の二射影の fiber 射を組にし、逆を fiber の包含の引き戻しで構成する。
規約：充填性は不要。使われ方：元の積図式の全空間比較の fiber を識別する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の引き戻しの二射影が誘導する、同じ頂点上の fiber の積同型。 -/
def fiberProductVertexIso {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.fst p q ≫ p) b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b := by
  let r := pullback.fst p q ≫ p
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap r p (pullback.fst p q) rfl b
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap r q (pullback.snd p q) (pullback.condition.symm) b
  let H := lift a c
  let L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b ⟶ pullback p q :=
    pullback.lift (fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) (by
    rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.comp_const, SSet.comp_const])
  have hL : L ≫ r = SSet.const b := by
    dsimp only [r]
    rw [← Category.assoc, show L ≫ pullback.fst p q = fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
      from pullback.lift_fst _ _ _, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift r b L hL
  have hV : V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r b = L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hHa : H ≫ fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r b ≫ pullback.fst p q := by
    rw [← Category.assoc, show H ≫ fst _ _ = a from lift_fst _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  have hHc : H ≫ snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r b ≫ pullback.snd p q := by
    rw [← Category.assoc, show H ≫ snd _ _ = c from lift_snd _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  refine { hom := H, inv := V, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext r b
    rw [Category.assoc, hV, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, show L ≫ pullback.fst p q = fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
        from pullback.lift_fst _ _ _, hHa]
    · rw [Category.assoc, show L ≫ pullback.snd p q = snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
        from pullback.lift_snd _ _ _, hHc]
  · apply CartesianMonoidalCategory.hom_ext
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
      rw [Category.assoc, Category.assoc, hHa, ← Category.assoc, hV, Category.id_comp]
      exact pullback.lift_fst _ _ _
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
      rw [Category.assoc, Category.assoc, hHc, ← Category.assoc, hV, Category.id_comp]
      exact pullback.lift_snd _ _ _

/-- fiber の積同型の第一射影は、元の引き戻しの第一射影の fiber 射。 -/
lemma fiberProductVertexIso_fst {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (b : B _⦋0⦌) :
    (fiberProductVertexIso p q b).hom ≫ fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.fst p q ≫ p) p (pullback.fst p q) rfl b := lift_fst _ _

/-- fiber の積同型の第二射影も、元の引き戻しの第二射影の fiber 射。 -/
lemma fiberProductVertexIso_snd {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (b : B _⦋0⦌) :
    (fiberProductVertexIso p q b).hom ≫ snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.fst p q ≫ p) q (pullback.snd p q) (pullback.condition.symm) b :=
  lift_snd _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
