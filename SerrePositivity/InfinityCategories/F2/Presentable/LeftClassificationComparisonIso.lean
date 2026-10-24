module

public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison

/-!
概要：同じ底上の left fibration の比較を全分類関手の同型へ送る。
方針：元の比較の各 fiber での同値性を全評価成分の可逆性へ移す。
規約：指定した全空間の射の分類を順射として保持する。
使われ方：随伴の Hom 族と comma の全自然な比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：fiber ごとに同値な比較の全分類射は可逆。
方針：同じ射の評価の可逆性を各 fiber から検出する。
規約：底の元の全分類図式を変えない。
使われ方：分類関手の比較同型。 -/
lemma leftClassificationHom_isIso_of_fibers {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsIso (leftClassificationHom p q f hf) := by
  apply functorHom_isIso_of_components
  rintro ⟨b⟩
  exact (leftClassificationHom_evaluation_isIso_iff p q f hf b).mpr (h b)

/-- 概要：fiber ごとの同値から元の全分類図式の自然同型を構成する。
方針：指定した全分類射の逆をホモトピー圏で取る。
規約：同型の順射は指定比較の分類そのもの。
使われ方：comma 模型での随伴 Hom の全自然な同型。 -/
def leftClassificationComparisonIso {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) := by
  have := leftClassificationHom_isIso_of_fibers p q f hf h
  exact asIso (leftClassificationHom p q f hf)

end SerrePositivity.InfinityCategories.F2.Presentable
