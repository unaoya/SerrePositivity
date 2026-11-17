module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberInclusion

/-!
概要：同じ fiber 包含の次数作用素と底の定値射影を回収する。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 同じ Grothendieck fiber 包含は、元のラベルの次数作用素を保つ。 -/
lemma sameSimplicialElementsFiberFunctor_degree {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I)
    {s t : (simplicialElementsCatDiagram G).obj i} (f : s ⟶ t) :
    ((simplicialElementsFiberFunctor G i).map f).hom.2 = f.down.hom := by
  let π : ULiftHom.{u} (G.obj i).Elements ⥤ SimplexCategoryᵒᵖ :=
    ULiftHom.down ⋙ Functor.Elements.π (G.obj i)
  change π.map ((Grothendieck.ι (simplicialElementsCatDiagram G) i).map f).fiber = π.map f
  dsimp only [Grothendieck.ι]
  rw [π.map_comp, eqToHom_map]
  change 𝟙 _ ≫ f.down.hom = f.down.hom
  exact Category.id_comp _

/-- 同じfiber包含の底への射影は、元の同じ頂点の定値関手。 -/
lemma sameSimplicialElementsFiberFunctor_projection {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I) :
    simplicialElementsFiberFunctor G i ⋙ simplicialTotalElementsProjection G =
      (CategoryTheory.Functor.const _).obj i := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro s t f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
