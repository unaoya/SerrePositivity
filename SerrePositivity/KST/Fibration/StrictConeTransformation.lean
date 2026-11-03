module
public import SerrePositivity.KST.Fibration.SizedDiagramTransformation
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-! # 元の頂点・全脚の通常の錐比較を、同じ全 coherent 錐の比較へ送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] {F G : I ⥤ C}

/-- 元の頂点射・全図式の変換・全脚の可換式を、始対象を加えた通常の変換にする。 -/
def strictConeTransformation (α : F ⟶ G) (c : Cone F) (d : Cone G) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ α.app i) :
    strictConeFunctor c ⟶ strictConeFunctor d where
  app j := match j with
    | WithInitial.star => f
    | WithInitial.of j => α.app (AsSmall.down.obj j)
  naturality {j k} t := by
    cases j with
    | star =>
      cases k with
      | star =>
        change 𝟙 c.pt ≫ f = f ≫ 𝟙 d.pt
        simp only [Category.id_comp, Category.comp_id]
      | of k => exact (hf (AsSmall.down.obj k)).symm
    | of j =>
      cases k with
      | star => exact PEmpty.elim t
      | of k => exact α.naturality (AsSmall.down.map t)

/-- 同じ join の錐の形を、始対象を加えた元の通常の添字へ送る射。 -/
def strictConeShapeMap :
    join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      nerve (WithInitial (AsSmall.{v} I)) :=
  joinMap (𝟙 Δ[0]) ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
    nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I))

/-- 頂点と全成分が可逆な同じ通常の比較は、全 coherent 錐の自然同型を与える。 -/
def strictCoherentConeTransformationIso [Quasicategory (SimplicialNerve C)]
    (α : F ⟶ G) (c : Cone F) (d : Cone G) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ α.app i)
    (hα : ∀ i, IsInvertibleEdge (coherentNerveEdge (α.app i)))
    (hfi : IsInvertibleEdge (coherentNerveEdge f)) :
    FunctorIso (strictCoherentCone c).val (strictCoherentCone d).val := by
  have he := sizedCoherentNatTransIso (strictConeTransformation α c d f hf) (by
    intro j
    cases j with
    | star => exact hfi
    | of j => exact hα (AsSmall.down.obj j))
  exact he.precomp (strictConeShapeMap (I := I))

/-- 同じ通常の錐比較の全成分の可逆性に沿って、実極限性を移す。 -/
theorem strictCoherentCone_isLimit_iff_of_transformation [Quasicategory (SimplicialNerve C)]
    (α : F ⟶ G) (c : Cone F) (d : Cone G) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ α.app i)
    (hα : ∀ i, IsInvertibleEdge (coherentNerveEdge (α.app i)))
    (hfi : IsInvertibleEdge (coherentNerveEdge f)) :
    IsLimitCone (strictCoherentCone c) ↔ IsLimitCone (strictCoherentCone d) :=
  ⟨fun h => h.of_functorIso (strictCoherentConeTransformationIso α c d f hf hα hfi),
    fun h => h.of_functorIso (strictCoherentConeTransformationIso α c d f hf hα hfi).symm⟩

end SerrePositivity.KST.Fibration
