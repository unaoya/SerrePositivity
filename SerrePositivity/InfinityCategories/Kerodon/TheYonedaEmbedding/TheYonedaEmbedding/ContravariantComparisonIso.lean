module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：反変図式間の指定比較同型を、表示同型で移した正方形へ運ぶ。
方針：元の同型を前後合成し、関手の合成則で両端を揃える。
規約：指定同型そのものを運び、別の同型を選ばない。
使われ方：局所 Hom 比較の共有面への自然性。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 表示同型で挟んだ比較は、元の可換正方形の同じ指定自然性を保持する。 -/
def contravariantComparisonIso {I : Type v} [Category.{w} I]
    (F G : Iᵒᵖ ⥤ SSet.{u}) [∀ z, Quasicategory (G.obj z)]
    {a b a' b' : I} (ea : a ≅ a') (eb : b ≅ b')
    (f : a ⟶ b) (g : a' ⟶ b') (h : ea.hom ≫ g = f ≫ eb.hom)
    (α : F.obj (Opposite.op a') ⟶ G.obj (Opposite.op a'))
    (β : F.obj (Opposite.op b') ⟶ G.obj (Opposite.op b'))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F.map g.op ≫ α) (β ≫ G.map g.op)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (F.map f.op ≫ (F.map ea.inv.op ≫ α ≫ G.map ea.hom.op))
      ((F.map eb.inv.op ≫ β ≫ G.map eb.hom.op) ≫ G.map f.op) := by
  have hi : ea.inv ≫ f = g ≫ eb.inv := by
    apply (cancel_mono eb.hom).1
    calc
      (ea.inv ≫ f) ≫ eb.hom = ea.inv ≫ (f ≫ eb.hom) := Category.assoc _ _ _
      _ = ea.inv ≫ (ea.hom ≫ g) := congrArg (fun t ↦ ea.inv ≫ t) h.symm
      _ = g := Iso.inv_hom_id_assoc ea g
      _ = (g ≫ eb.inv) ≫ eb.hom := by simp
  have hF : F.map f.op ≫ F.map ea.inv.op = F.map eb.inv.op ≫ F.map g.op := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg (fun t ↦ F.map t.op) hi
  have hG : G.map g.op ≫ G.map ea.hom.op = G.map eb.hom.op ≫ G.map f.op := by
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg (fun t ↦ G.map t.op) h
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((e.precomp (F.map eb.inv.op)).postcomp (G.map ea.hom.op))
  · simp only [← Category.assoc]
    rw [← hF]
  · simp only [Category.assoc]
    rw [hG]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
