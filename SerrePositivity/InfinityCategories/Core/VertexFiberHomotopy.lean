module

public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：基底上で定値なホモトピーの fiber への制限。
方針：直積上のホモトピーを fiber の普遍性で持ち上げる。
規約：同じ基底の射を全時刻で厳密に固定する。
使われ方：Kerodon §4.5.3 の fiber の比較のホモトピー逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：基底上で定値なホモトピーは各 fiber のホモトピーへ制限できる。
方針：fiber の包含との直積に沿って制限し、標的の fiber へ持ち上げる。
規約：元の二つの射は同じ基底上の射。
使われ方：Kerodon §4.5.3 の fiber 内の変形。 -/
def vertexFiberHomotopy {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    {f g : E ⟶ F} (hf : f ≫ q = p) (hg : g ≫ q = p) (H : SSet.Homotopy f g)
    (hH : H.h ≫ q = fst E (Δ[1] : SSet.{u}) ≫ p) (b : B _⦋0⦌) :
    SSet.Homotopy (vertexFiberMap p q f hf b) (vertexFiberMap p q g hg b) where
  h := vertexFiberLift q b ((vertexFiberι p b ▷ (Δ[1] : SSet.{u})) ≫ H.h) (by
    rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst, Category.assoc,
      vertexFiberι_comp, SSet.comp_const])
  h₀ := by
    apply vertexFiber_hom_ext q b
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, SSet.ι₀_comp, Category.assoc,
      H.h₀]
    exact (vertexFiberMap_ι p q f hf b).symm
  h₁ := by
    apply vertexFiber_hom_ext q b
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
      H.h₁]
    exact (vertexFiberMap_ι p q g hg b).symm

  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：点ごとに可逆な基底上のホモトピーは fiber 上でも点ごとに可逆。
方針：fiber の包含への像を元のホモトピーの頂点辺と比較し、可逆性を反映する。
規約：標的 F と基底 B は quasicategory、q は inner fibration。
使われ方：Kerodon §4.5.3 の fiber 内の自然同型。 -/
lemma vertexFiberHomotopy_isInvertible {E F B : SSet.{u}}
    [Quasicategory F] [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
    {f g : E ⟶ F} (hf : f ≫ q = p) (hg : g ≫ q = p) (H : SSet.Homotopy f g)
    (hH : H.h ≫ q = fst E (Δ[1] : SSet.{u}) ≫ p)
    (hI : ∀ x : E _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated)
    (b : B _⦋0⦌) (x : (vertexFiber p b) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (vertexFiberHomotopy p q hf hg H hH b) x).toTruncated := by
  apply (isInvertibleEdge_vertexFiber_iff q b _).2
  exact (isInvertibleEdge_congr rfl).2 (hI x.val)

end SerrePositivity.InfinityCategories
