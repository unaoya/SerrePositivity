module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：通常射の単位からの豊穣表示は、元の前後合成を全単体で保つ。
方針：単位からの射の定数単体の式と既存の定数合成則を使う。
規約：IS-W2 D01の既存構成の単位・合成則。新しい射の表示を選ばない。
使われ方：Kerodon 7.5.4、同じweighted coneの頂点・尾部の厳密自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 同じ通常射の豊穣表示は、元の後合成を保つ。 -/
theorem closedVertex_whiskerLeft {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv SSet f ≫ eHomWhiskerLeft SSet x g = eHomEquiv SSet (f ≫ g) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have hs : s = PUnit.unit := by exact @Subsingleton.elim PUnit inferInstance _ _
  subst s
  change (eComp SSet x y z).app (Opposite.op ⦋n⦌)
    ((eHomEquiv SSet f).app _ PUnit.unit, (eHomEquiv SSet g).app _ PUnit.unit) =
      (eHomEquiv SSet (f ≫ g)).app _ PUnit.unit
  simp only [unitHom_app_constant]
  exact simplicialHom_constant_comp f g n

/-- 同じ通常射の豊穣表示は、元の前合成を保つ。 -/
theorem closedVertex_whiskerRight {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f z = eHomEquiv SSet (f ≫ g) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have hs : s = PUnit.unit := by exact @Subsingleton.elim PUnit inferInstance _ _
  subst s
  change (eComp SSet x y z).app (Opposite.op ⦋n⦌)
    ((eHomEquiv SSet f).app _ PUnit.unit, (eHomEquiv SSet g).app _ PUnit.unit) =
      (eHomEquiv SSet (f ≫ g)).app _ PUnit.unit
  simp only [unitHom_app_constant]
  exact simplicialHom_constant_comp f g n

/-- 同じ閉射は、両端の単位の豊穣作用に厳密に可換する。 -/
theorem enrichedUnit_whiskering {x y : C} (f : x ⟶ y) :
    eId SSet x ≫ eHomWhiskerLeft SSet x f =
      eId SSet y ≫ eHomWhiskerRight SSet f y := by
  rw [← eHomEquiv_id, ← eHomEquiv_id, closedVertex_whiskerLeft, closedVertex_whiskerRight,
    Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
