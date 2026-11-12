module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-! # A natural cosimplicial frame over the actual homotopy colimit

Resolve the projective cofibrant replacement in the cosimplicial direction,
then take actual colimits degreewise. Colimit is left Quillen, so this is a
Reedy cofibrant, homotopically constant diagram weakly augmented over the
specified homotopy colimit. No tensor or enrichment on the source is used.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.ColimitFrame
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w,w} C := Smith.locallyPresentable_hasColimits (C := C)

def resolutionFamily :
    let := Projective.modelCategory K I J
    CofibrantResolutionFamily (C := K ⥤ C) simplex := by
  let := Projective.modelCategory K I J
  exact cosimplicialResolutionFamily (HomotopyColimit.cofibrantFactorization K I J)

abbrev diagramResolution : (K ⥤ C) ⥤ (SimplexCategory ⥤ K ⥤ C) := by
  let := Projective.modelCategory K I J
  exact HomotopyColimit.replacement K I J ⋙ (resolutionFamily K I J).obj

abbrev frame : (K ⥤ C) ⥤ (SimplexCategory ⥤ C) :=
  diagramResolution K I J ⋙ (Functor.whiskeringRight SimplexCategory (K ⥤ C) C).obj colim

def augmentation : frame K I J ⟶ HomotopyColimit.functor K I J ⋙
    (Functor.const SimplexCategory : C ⥤ SimplexCategory ⥤ C) := by
  let := Projective.modelCategory K I J
  exact {
  app F := {
    app n := colim.map (((resolutionFamily K I J).augmentation.app
      ((HomotopyColimit.replacement K I J).obj F)).app n)
    naturality n m f := by
      have h := ((resolutionFamily K I J).augmentation.app
        ((HomotopyColimit.replacement K I J).obj F)).naturality f
      change colim.map (((diagramResolution K I J).obj F).map f) ≫
          colim.map (((resolutionFamily K I J).augmentation.app
            ((HomotopyColimit.replacement K I J).obj F)).app m) =
        colim.map (((resolutionFamily K I J).augmentation.app
          ((HomotopyColimit.replacement K I J).obj F)).app n) ≫ 𝟙 _
      rw [Category.comp_id, ← colim.map_comp]
      exact congrArg colim.map (h.trans (Category.comp_id _)) }
  naturality F G f := by
    apply NatTrans.ext
    funext n
    have h := congr_app ((resolutionFamily K I J).augmentation.naturality
      ((HomotopyColimit.replacement K I J).map f)) n
    change colim.map (((diagramResolution K I J).map f).app n) ≫
        colim.map (((resolutionFamily K I J).augmentation.app
          ((HomotopyColimit.replacement K I J).obj G)).app n) =
      colim.map (((resolutionFamily K I J).augmentation.app
          ((HomotopyColimit.replacement K I J).obj F)).app n) ≫
        colim.map ((HomotopyColimit.replacement K I J).map f)
    rw [← colim.map_comp, ← colim.map_comp]
    exact congrArg colim.map h }

lemma reedyCofibrant (F : K ⥤ C) :
    reedyLeft simplex (cofibrations C) (initial.to ((frame K I J).obj F)) := by
  let := Projective.modelCategory K I J
  have := Projective.colimit_isLeftQuillen K I J
  exact leftQuillen_frame_reedyCofibrant (colim : (K ⥤ C) ⥤ C)
    ((diagramResolution K I J).obj F)
    ((resolutionFamily K I J).cofibrant ((HomotopyColimit.replacement K I J).obj F))

lemma homotopicallyConstant (F : K ⥤ C) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (((frame K I J).obj F).map f) := by
  let := Projective.modelCategory K I J
  have := Projective.colimit_isLeftQuillen K I J
  let q := (resolutionFamily K I J).atObject ((HomotopyColimit.replacement K I J).obj F)
  exact leftQuillen_frame_homotopicallyConstant (colim : (K ⥤ C) ⥤ C) q.obj q.cofibrant
    q.homotopicallyConstant f

lemma augmentation_weakEquivalence (F : K ⥤ C) (n : SimplexCategory) :
    weakEquivalences C (((augmentation K I J).app F).app n) := by
  let := Projective.modelCategory K I J
  have := Projective.colimit_isLeftQuillen K I J
  have := HomotopyColimit.replacement_isCofibrant K I J F
  let q := (resolutionFamily K I J).atObject ((HomotopyColimit.replacement K I J).obj F)
  exact leftQuillen_frame_augmentation_weakEquivalence (colim : (K ⥤ C) ⥤ C)
    q.obj q.cofibrant q.augmentation q.augmentation_weakEquivalence n

lemma hom_kanComplex (F : K ⥤ C) (Y : C) [IsFibrant Y] :
    SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((frame K I J).obj F)).obj Y) :=
  cosimplicialHom_kanComplex _ (reedyCofibrant K I J F) (homotopicallyConstant K I J F) Y

/-- The actual colimit/constant adjunction identifies all simplices, in the
common universe of diagram morphisms and source morphisms. -/
def homIso (F : K ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((frame K I J).obj F) ⋙ SSet.uliftFunctor.{max w v,v} ≅
      (Functor.const K : C ⥤ K ⥤ C) ⋙
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((diagramResolution K I J).obj F) ⋙ SSet.uliftFunctor.{v,max w v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso (colimConstAdj (J := K) (C := C)) ((diagramResolution K I J).obj F)

@[reassoc]
lemma homIso_source_naturality {F G : K ⥤ C} (f : F ⟶ G) :
    Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((frame K I J).map f))
        SSet.uliftFunctor.{max w v,v} ≫ (homIso K I J F).hom =
      (homIso K I J G).hom ≫ Functor.whiskerLeft (Functor.const K : C ⥤ K ⥤ C)
        (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((diagramResolution K I J).map f))
          SSet.uliftFunctor.{v,max w v}) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso_source_naturality (colimConstAdj (J := K) (C := C))
    ((diagramResolution K I J).map f)

end SerrePositivity.DiagramModel.ColimitFrame
