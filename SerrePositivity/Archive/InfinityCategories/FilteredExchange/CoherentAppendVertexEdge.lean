module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentAppendLastPreserving
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-!
概要：元の頂点へ指定射を追加すると、元の同じ coherent な射の辺になる。
方針：一単体の射データを豊穣恒等の後合成で計算する。
規約：指定射の辺を選び直さない。使われ方：追加した全錐族の固定終辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の豊穣恒等を指定射で後合成すると、その同じ指定射の豊穣像になる。 -/
lemma simplicialIdentity_postcompose {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (g : X ⟶ Y) :
    eId SSet X ≫ eHomWhiskerLeft SSet X g = eHomEquiv SSet g := by
  rw [eHomWhiskerLeft, ← eHomEquiv_id, ← Category.assoc, rightUnitor_inv_naturality]
  rw [Category.assoc, ← tensorHom_def_assoc, ← unitors_inv_equal,
    ← eHomEquiv_comp, Category.id_comp]

/-- 元の頂点への指定射の追加は、同じ指定射の元の coherent 辺。 -/
lemma coherentSimplexAppendMorphism_vertex
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} (g : X ⟶ Y) :
    coherentSimplexAppendMorphism (coherentNerveVertex X) g = (coherentNerveEdge g).edge := by
  apply (coherentNerveArrowDataEquiv C).injective
  change coherentNerveArrowData (coherentSimplexAppendMorphism (coherentNerveVertex X) g) =
    coherentNerveArrowData ((coherentNerveEdge g).edge)
  rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow]
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    (((toUnit (nerve (Path (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) (ULift.up 1))) ≫
      eId SSet X) ≫ eHomWhiskerLeft SSet X ((𝟙 X) ≫ g)).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ coherentOnePath))⟩ : Σ A B : C, A ⟶ B) = _
  rw [Category.id_comp, Category.assoc, simplicialIdentity_postcompose]
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    (SimplicialCategory.homEquiv' X Y g)⟩ : Σ A B : C, A ⟶ B) = _
  rw [Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.F2
