module
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.StrictCoherentNatTransComponent
public import Mathlib.CategoryTheory.Functor.Currying

/-! # 大きい通常の錐添字の、元の成分を保つ coherent な自然変換 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {J : Type (max u v)} [SmallCategory J] {F G : J ⥤ C}

/-- 大きい通常の添字の変換を、同じ元の全射列上の区間族へ送る。 -/
def sizedNatTransMap (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve J ⟶ nerve C where
  app n := ↾fun z => ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2) ⋙
    CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply CategoryTheory.Functor.ext (fun _ => rfl)

omit [SimplicialCategory C] in
/-- 区間族の始点は、元の通常の始域関手である。 -/
theorem sizedNatTransMap_zero (η : F ⟶ G) :
    prismEndpoint 0 (nerve J) ≫ sizedNatTransMap η = resizedNerveMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ F.map (s.map _) = F.map (s.map _)
    exact Category.id_comp _

omit [SimplicialCategory C] in
/-- 区間族の終点は、元の通常の終域関手である。 -/
theorem sizedNatTransMap_one (η : F ⟶ G) :
    prismEndpoint 1 (nerve J) ≫ sizedNatTransMap η = resizedNerveMap G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ G.map (s.map _) = G.map (s.map _)
    exact Category.id_comp _

omit [SimplicialCategory C] in
/-- 各元の対象における区間辺は、指定した元の通常成分の辺そのもの。 -/
theorem sizedNatTransMap_component (η : F ⟶ G) (j : J) :
    (sizedNatTransMap η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        PinchedHom.constant (nerveVertex j) 1) = (nerve.edgeMk (η.app j)).edge := by
  apply ComposableArrows.ext₁
  case left => rfl
  case right => rfl
  case w =>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app j ≫ G.map (𝟙 j) = η.app j
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- 全成分が coherent に可逆な通常変換は、同じ全図式の自然同型を与える。 -/
def sizedCoherentNatTransIso [Quasicategory (SimplicialNerve C)] (η : F ⟶ G)
    (hη : ∀ j, IsInvertibleEdge (coherentNerveEdge (η.app j))) :
    FunctorIso (resizedNerveMap F ≫ nerveToCoherent C)
      (resizedNerveMap G ≫ nerveToCoherent C) := by
  let H := sizedNatTransMap η ≫ nerveToCoherent C
  have e := functorIsoOfEquivalenceHomotopy H (by
    intro x
    have hx : x = nerveVertex (x.obj 0) := ComposableArrows.ext₀ rfl
    rw [hx]
    change IsInvertibleEdge (edgeOfSimplex ((nerveToCoherent C).app (Opposite.op ⦋1⦌)
      ((sizedNatTransMap η).app (Opposite.op ⦋1⦌) _)))
    rw [sizedNatTransMap_component]
    exact (isInvertibleEdge_congr (e := edgeOfSimplex _)
      (f := coherentNerveEdge (η.app (x.obj 0))) rfl).mpr (hη _))
  have h0 : prismEndpoint 0 (nerve J) ≫ H = resizedNerveMap F ≫ nerveToCoherent C := by
    change prismEndpoint 0 (nerve J) ≫ (sizedNatTransMap η ≫ nerveToCoherent C) = _
    rw [← Category.assoc, sizedNatTransMap_zero]
  have h1 : prismEndpoint 1 (nerve J) ≫ H = resizedNerveMap G ≫ nerveToCoherent C := by
    change prismEndpoint 1 (nerve J) ≫ (sizedNatTransMap η ≫ nerveToCoherent C) = _
    rw [← Category.assoc, sizedNatTransMap_one]
  rw [h0, h1] at e
  exact e

end SerrePositivity.KST.Fibration
