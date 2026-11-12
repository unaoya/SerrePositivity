module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：基底上で定値なホモトピーの fiber への制限。
方針：直積上のホモトピーを fiber の普遍性で持ち上げる。
規約：同じ基底の射を全時刻で厳密に固定する。
使われ方：Kerodon §4.5.3（Tag 032Y） の fiber の比較のホモトピー逆。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：基底上で定値なホモトピーは各 fiber のホモトピーへ制限できる。
方針：fiber の包含との直積に沿って制限し、標的の fiber へ持ち上げる。
規約：元の二つの射は同じ基底上の射。
使われ方：Kerodon §4.5.3（Tag 032Y） の fiber 内の変形。 -/
def vertexFiberHomotopy {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    {f g : E ⟶ F} (hf : f ≫ q = p) (hg : g ≫ q = p) (H : SSet.Homotopy f g)
    (hH : H.h ≫ q = fst E (Δ[1] : SSet.{u}) ≫ p) (b : B _⦋0⦌) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q g hg b) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ▷ (Δ[1] : SSet.{u})) ≫ H.h) (by
    rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const])
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, SSet.ι₀_comp, Category.assoc,
      H.h₀]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι p q f hf b).symm
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
      H.h₁]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι p q g hg b).symm

  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：点ごとに可逆な基底上のホモトピーは fiber 上でも点ごとに可逆。
方針：fiber の包含への像を元のホモトピーの頂点辺と比較し、可逆性を反映する。
規約：標的 F と基底 B は quasicategory、q は inner fibration。
使われ方：Kerodon §4.5.3（Tag 032Y） の fiber 内の自然同型。 -/
lemma vertexFiberHomotopy_isInvertible {E F B : SSet.{u}}
    [Quasicategory F] [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
    {f g : E ⟶ F} (hf : f ≫ q = p) (hg : g ≫ q = p) (H : SSet.Homotopy f g)
    (hH : H.h ≫ q = fst E (Δ[1] : SSet.{u}) ≫ p)
    (hI : ∀ x : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)
    (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (vertexFiberHomotopy p q hf hg H hH b) x).toTruncated := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_vertexFiber_iff q b _).2
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl).2 (hI x.val)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
