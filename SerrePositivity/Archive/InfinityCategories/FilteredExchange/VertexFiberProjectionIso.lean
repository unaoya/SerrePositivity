module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：射影の明示した等式で同じ頂点 fiber の二つの表示を厳密に同定する。
方針：等式による対象の同型を使い、包含と元の fiber 射に対する自然性を確認する。
規約：射影の等式を入力に保持。使われ方：模型の入力 fiber と元の図式の fiber の表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ射影の二つの表示に沿う、元の同じ頂点 fiber の同型。 -/
def vertexFiberProjectionIso {E B : SSet.{u}} (p q : E ⟶ B) (h : p = q) (b : B _⦋0⦌) :
    vertexFiber p b ≅ vertexFiber q b := eqToIso (congrArg (fun r => vertexFiber r b) h)

/-- 射影表示の同型は、元の全空間への包含を厳密に保つ。 -/
lemma vertexFiberProjectionIso_hom_ι {E B : SSet.{u}} (p q : E ⟶ B) (h : p = q)
    (b : B _⦋0⦌) :
    (vertexFiberProjectionIso p q h b).hom ≫ vertexFiberι q b = vertexFiberι p b := by
  subst q
  simp only [vertexFiberProjectionIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- 標的射影の表示変更は、元の同じ fiber 射を保つ。 -/
lemma vertexFiberMap_target_projection {E F B : SSet.{u}} (p : E ⟶ B) (q q' : F ⟶ B)
    (h : q = q') (f : E ⟶ F) (hf : f ≫ q = p) (hf' : f ≫ q' = p) (b : B _⦋0⦌) :
    vertexFiberMap p q f hf b ≫ (vertexFiberProjectionIso q q' h b).hom =
      vertexFiberMap p q' f hf' b := by
  subst q'
  simp only [vertexFiberProjectionIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 始域射影の表示変更も、元の同じ fiber 射を保つ。 -/
lemma vertexFiberMap_source_projection {E F B : SSet.{u}} (p p' : E ⟶ B) (q : F ⟶ B)
    (h : p = p') (f : E ⟶ F) (hf : f ≫ q = p) (hf' : f ≫ q = p') (b : B _⦋0⦌) :
    (vertexFiberProjectionIso p p' h b).hom ≫ vertexFiberMap p' q f hf' b =
      vertexFiberMap p q f hf b := by
  subst p'
  simp only [vertexFiberProjectionIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
