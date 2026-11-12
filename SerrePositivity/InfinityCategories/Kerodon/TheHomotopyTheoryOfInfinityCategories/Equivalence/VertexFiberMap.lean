module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：同じ基底上の射が誘導する頂点の fiber の射。
方針：元の射を fiber から含め、標的の fiber の普遍性で持ち上げる。
規約：射の等式で基底を厳密に固定する。
使われ方：Kerodon Corollary 4.5.3.31（Tag 01HK） の fiber の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：基底を保つ射は各頂点上の fiber の射を誘導する。
方針：fiber への持ち上げを使う。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の固定図式の比較。 -/
def vertexFiberMap {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F)
    (hf : f ≫ q = p) (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ f) (by rw [Category.assoc, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp])

/-- 概要：fiber の誘導射を元の標的に含めると元の射との合成。
方針：fiber の持ち上げの計算。
規約：基底の可換性の証明の選択は問わない。
使われ方：Kerodon §4.5.3（Tag 032Y） の比較の等式。 -/
lemma vertexFiberMap_ι {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F)
    (hf : f ≫ q = p) (b : B _⦋0⦌) :
    vertexFiberMap p q f hf b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ f := rfl

/-- 概要：恒等射が誘導する fiber の射は恒等。
方針：包含後に比較する。
規約：任意の基底の頂点を扱う。
使われ方：Kerodon §4.5.3（Tag 032Y） の fiber の射の関手性。 -/
lemma vertexFiberMap_id {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiberMap p p (𝟙 E) (by simp) b = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [vertexFiberMap_ι, Category.comp_id, Category.id_comp]

/-- 概要：fiber の誘導射は合成を保つ。
方針：包含後に元の射の合成を計算する。
規約：三つの対象は同じ基底への射を持つ。
使われ方：Kerodon §4.5.3（Tag 032Y） の fiber の射の関手性。 -/
lemma vertexFiberMap_comp {E F G B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (r : G ⟶ B)
    (f : E ⟶ F) (g : F ⟶ G) (hf : f ≫ q = p) (hg : g ≫ r = q) (b : B _⦋0⦌) :
    vertexFiberMap p q f hf b ≫ vertexFiberMap q r g hg b =
      vertexFiberMap p r (f ≫ g) (by rw [Category.assoc, hg, hf]) b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext r b
  rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, vertexFiberMap_ι,
    vertexFiberMap_ι, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
