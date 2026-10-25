module

public import SerrePositivity.InfinityCategories.F1.Diagrams.KanWeightedUnstraighteningUnit
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom

/-!
概要：直値 Kan 図式の全空間単位の相対回収を、各 fiber の共通解像へ厳密に制限する。
方針：同じ相対関手空間の同型を fiber Hom に写し、係数変換の自然性で両端を計算する。
規約：全空間射を選び直さず、底と全次数の fiber 写像を固定する。
使われ方：Ind-S (5) の指定値回収への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 相対的に回収された同じ実射は、全 fiber の共通解像でも同じ比較を回収する。 -/
def kanWeightedUnstraighteningUnit_fiber_commonIso
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u})
    (f : weightedNerve (F ⋙ kanObjectForget) ⟶
      smallLeftUnstraightening (kanDiagramCoherentNerve F))
    (hf : f ≫ smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F) =
      weightedNerveProjection (F ⋙ kanObjectForget))
    (e : VertexIso
      (relativeFunctorVertex (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget))
        (weightedKanEdgewiseRight F ≫ f)
        (by rw [Category.assoc, hf, weightedKanEdgewiseRight_projection]))
      (relativeFunctorVertex (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget))
        (weightedKanEdgewiseLeft F ≫ smallReversedWeightedKanUnstraighteningComparison F)
        (by rw [Category.assoc, smallReversedWeightedKanUnstraighteningComparison_projection,
          weightedKanEdgewiseLeft_projection]))) (c : I) :
    FunctorIso
      (edgewiseRight (F.obj c).obj ≫ weightedNerveFiberMap (F ⋙ kanObjectForget) c ≫
        vertexFiberMap _ _ f hf (nerveVertex c))
      (edgewiseLeft (F.obj c).obj ≫
        weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c ≫
        vertexFiberMap _ _ (smallReversedWeightedKanUnstraighteningComparison F)
          (smallReversedWeightedKanUnstraighteningComparison_projection F) (nerveVertex c)) := by
  have h := e.map (relativeFunctorFiberHom
    (weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget))
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F)) (nerveVertex c))
  rw [relativeFunctorFiberHom_vertex, relativeFunctorFiberHom_vertex] at h
  have h' := FunctorIso.precomp h
    (weightedNerveFiberMap (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget) c)
  rw [← vertexFiberMap_comp _ (weightedNerveProjection (F ⋙ kanObjectForget)) _
    (weightedKanEdgewiseRight F) f (weightedKanEdgewiseRight_projection F) hf,
    ← vertexFiberMap_comp _
      (weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget)) _
      (weightedKanEdgewiseLeft F) (smallReversedWeightedKanUnstraighteningComparison F)
      (weightedKanEdgewiseLeft_projection F)
      (smallReversedWeightedKanUnstraighteningComparison_projection F)] at h'
  have hr := weightedNerveMap_fiber_naturality
    (Functor.whiskerRight (Functor.whiskerLeft F kanEdgewiseRight) kanObjectForget) c
  have hl := weightedNerveMap_fiber_naturality
    (Functor.whiskerRight (Functor.whiskerLeft F kanEdgewiseLeft) kanObjectForget) c
  dsimp only [weightedKanEdgewiseRight, weightedKanEdgewiseLeft] at h'
  simp only [← Category.assoc] at h'
  erw [hr, hl] at h'
  simpa only [Category.assoc, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    kanEdgewiseRight, kanEdgewiseLeft, kanObjectForget, kanEdgewiseFunctor,
    Functor.comp_obj, Functor.comp_id, Functor.assoc] using h'

end SerrePositivity.InfinityCategories
