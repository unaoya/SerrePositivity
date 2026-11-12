module

public import SerrePositivity.KST.Spectra.D3EndpointParameterSquare
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage

/-!
概要：全パラメータ四角形族の各実頂点を、同じ通常の制限射の strict な図式へ照合する。
方針：混合 Hom の恒等入力を元の自然変換成分へ戻し、全次数の定値 Hom を比較する。
規約：四角形を頂点だけで比較せず、全単体で同じ通常図式の coherent 表示へ接続する。
使われ方：d3 の実端点パラメータ族の loop 性の認証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

section
variable {C : Type v} {E : Type w} [EnrichedCategory SSet.{u} C]
  [EnrichedCategory SSet.{u} E] {F G : EnrichedFunctor SSet.{u} C E}

/-- 混合 Hom の実恒等入力は、同じ自然変換成分そのもの。 -/
lemma d3Mixed_identity (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (X : C) : eId SSet X ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η X X = η.app X := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟩
  have hi := ConcreteCategory.congr_hom (NatTrans.congr_app (G.map_id X) d) PUnit.unit
  change (G.map X X).app d ((eId SSet X).app d PUnit.unit) =
    (eId SSet (G.obj X)).app d PUnit.unit at hi
  change (eComp SSet (F.obj X) (G.obj X) (G.obj X)).app d
    ((η.app X).app d PUnit.unit, (G.map X X).app d ((eId SSet X).app d PUnit.unit)) = _
  rw [hi]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (e_comp_id SSet (F.obj X) (G.obj X)) d)
      ((η.app X).app d PUnit.unit)

end

local instance d3ParameterVertexPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory
local instance d3ParameterVertexSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)

variable {J : Type v} [Preorder J] (D : Jᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 同じ実パラメータ射を一つの Kan 入力で評価した通常の図式。 -/
def d3ParameterEvaluation (X : PointedKanObject.{u}) : J ⥤ PointedKanObject.{u} where
  obj i := (d3PointedKanIhom (D.obj (Opposite.op i))).obj X
  map {i j} f := ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (D.map f.op) X.obj)
  map_id i := by
    apply ObjectProperty.hom_ext
    change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (D.map (𝟙 (Opposite.op i))) X.obj = 𝟙 _
    rw [D.map_id, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact (internalHom.flip.obj X.obj).map_id (Opposite.op (D.obj (Opposite.op i)))
  map_comp {i j k} f g := by
    apply ObjectProperty.hom_ext
    change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (D.map (g.op ≫ f.op)) X.obj =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (D.map f.op) X.obj ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (D.map g.op) X.obj
    rw [D.map_comp]
    exact (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp (D.map g.op) (D.map f.op) X.obj).symm

/-- 同じ実パラメータ射の混合 Hom は、恒等入力で元の制限射を回収する。 -/
lemma d3ParameterMixed_identity (i j : J) (h : i ≤ j) (X : PointedKanObject.{u}) :
    eId SSet X ≫ d3ParameterMixed D i j h X X =
      eHomEquiv SSet ((d3ParameterEvaluation D X).map (homOfLE h)) :=
  d3Mixed_identity (d3PointedKanPre (d3ParameterArrow D h)) X


/-- 同じ通常のパラメータ射を四角形の全単体で並べた通常 nerve の図式。 -/
def d3ParameterOrdinarySquare
    (D : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u}) (X : PointedKanObject.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶ nerve PointedKanObject.{u} where
  app _ := ↾fun t ↦ (d3ParameterSquareOrder t).toFunctor ⋙ d3ParameterEvaluation D X
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro t
    rfl

/-- 全族の実頂点の四角形は、同じ通常図式の coherent 表示そのもの。 -/
lemma d3PointedKanParameterSquare_vertex
    (D : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u}) (X : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((d3PointedKanParameterSquare D).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) =
      d3ParameterOrdinarySquare D X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent PointedKanObject.{u} := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply EnrichedFunctor.ext SSet
  case h_obj => intro k; rfl
  case h_map =>
    intro k l
    simp only [eqToHom_refl, Category.comp_id]
    apply SSet.hom_ext
    rintro ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro P
    change (D3EnrichedOrderedDiagram.map (d3ParameterStage D) (d3ParameterMixed D)
      (⟨d3ParameterSquareOrder t k.as.down, X⟩ :
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2 × Fin 2) PointedKanObject.{u})
      ⟨d3ParameterSquareOrder t l.as.down, X⟩).app _
      ((EnrichedOrderedCylinder.pathOrderMap (d3ParameterSquareOrder t) k l).app _ P,
        (eId SSet X).app _ PUnit.unit) = _
    rw [D3EnrichedOrderedDiagram.map_app]
    have hm := ConcreteCategory.congr_hom (NatTrans.congr_app
      (d3ParameterMixed_identity D _ _
        ((EnrichedOrderedCylinder.pathOrderMap (d3ParameterSquareOrder t) k l).app _ P).down.down X)
      (Opposite.op ⦋m⦌)) PUnit.unit
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hm
    rw [hm]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant _ m

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
