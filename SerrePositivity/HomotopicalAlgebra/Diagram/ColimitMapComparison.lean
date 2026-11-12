module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-! # Comparing actual RMap of hocolim with its colimit frame Hom

Both bifunctors map naturally by weak equivalences to the Hom of one
actual common frame. The source is any combinatorial model category;
no simplicial enrichment is assumed. The comparison is compatible with
the colimit/constant simplicial Hom isomorphism in ColimitFrame.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.ColimitMapComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

local instance : HasColimitsOfSize.{w,w} C := Smith.locallyPresentable_hasColimits (C := C)

abbrev commonFrame := FrameOverFunctor.commonObj cof (cosimplicialResolutionFamily cof)
  (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J) (ColimitFrame.augmentation K I J)

abbrev middle : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} :=
  FrameOverFunctor.hom (commonFrame K I J cof) ⋙
    (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib)

abbrev frameHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} :=
  FrameOverFunctor.hom (ColimitFrame.frame K I J) ⋙
    (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib)

abbrev left : (HomotopyColimit.functor K I J).op ⋙ chosenResolutionHom cof fib ⟶
    middle K I J cof fib :=
  Functor.whiskerRight
    (FrameOverFunctor.homLeft cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J) (ColimitFrame.augmentation K I J))
    ((Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib))

abbrev right : frameHom K I J fib ⟶ middle K I J cof fib :=
  Functor.whiskerRight
    (FrameOverFunctor.homRight cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J) (ColimitFrame.augmentation K I J))
    ((Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib))

lemma middle_kanComplex (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    SSet.KanComplex (((middle K I J cof fib).obj F).obj Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact cosimplicialHom_kanComplex _
    (FrameOverFunctor.commonObj_cofibrant cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J)
      (ColimitFrame.augmentation K I J) F.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J)
      (ColimitFrame.augmentation K I J) (ColimitFrame.augmentation_weakEquivalence K I J) F.unop) _

/-- Diagram-resolution Hom into the actual constant fibrant target. -/
abbrev diagramHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{max w v} :=
  FrameOverFunctor.hom (ColimitFrame.diagramResolution K I J) ⋙
    (Functor.whiskeringLeft C (K ⥤ C) SSet.{max w v}).obj
      (fibrantTarget fib ⋙ (Functor.const K : C ⥤ K ⥤ C))

/-- The actual adjunction comparison, natural in both the input diagram and
original target. Both Hom universes are explicitly lifted to their maximum. -/
def liftedHomIso :
    frameHom K I J fib ⋙
        (Functor.whiskeringRight C SSet.{v} SSet.{max w v}).obj
          SSet.uliftFunctor.{max w v,v} ≅
      diagramHom K I J fib ⋙
        (Functor.whiskeringRight C SSet.{max w v} SSet.{max w v}).obj
          SSet.uliftFunctor.{v,max w v} :=
  NatIso.ofComponents (fun F =>
    Functor.isoWhiskerLeft (fibrantTarget fib) (ColimitFrame.homIso K I J F.unop)) (by
      intro F G f
      ext Y n h
      apply ULift.ext
      exact (colimConstAdj (J := K) (C := C)).homEquiv_naturality_left
        (((ColimitFrame.diagramResolution K I J).map f.unop).app n.unop) h.down)

lemma constantTarget_isFibrant (Y : C) :
    let := Projective.modelCategory K I J
    IsFibrant ((fibrantTarget fib ⋙ (Functor.const K : C ⥤ K ⥤ C)).obj Y) := by
  let := Projective.modelCategory K I J
  let R := (Functor.const K : C ⥤ K ⥤ C)
  have : R.IsRightAdjoint := (colimConstAdj (J := K) (C := C)).isRightAdjoint
  have : Quillen.IsRightQuillen R := Projective.constant_isRightQuillen K I J
  have := fibrantTarget_isFibrant fib Y
  exact (isFibrant_iff_of_isTerminal (R.map (terminal.from ((fibrantTarget fib).obj Y)))
    (terminalIsTerminal.isTerminalObj R (⊤_ C))).mpr
    (Quillen.map_fibration R (terminal.from ((fibrantTarget fib).obj Y)))

lemma diagramHom_kanComplex (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    SSet.KanComplex (((diagramHom K I J fib).obj F).obj Y) := by
  let := Projective.modelCategory K I J
  have := constantTarget_isFibrant K I J fib Y
  let q := (ColimitFrame.resolutionFamily K I J).atObject
    ((HomotopyColimit.replacement K I J).obj F.unop)
  exact cosimplicialHom_kanComplex q.obj q.cofibrant q.homotopicallyConstant _

/-- The ordinary resolution of the original input diagram, with target
already fibrant via the constant source fibrant replacement. -/
def originalDiagramHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{max w v} := by
  let := Projective.modelCategory K I J
  exact FrameOverFunctor.hom (ColimitFrame.resolutionFamily K I J).obj ⋙
    (Functor.whiskeringLeft C (K ⥤ C) SSet.{max w v}).obj
      (fibrantTarget fib ⋙ (Functor.const K : C ⥤ K ⥤ C))

/-- The actual diagram replacement comparison induces a natural source map. -/
def diagramSourceComparison : originalDiagramHom K I J fib ⟶ diagramHom K I J fib := by
  let := Projective.modelCategory K I J
  let a : ColimitFrame.diagramResolution K I J ⟶ (ColimitFrame.resolutionFamily K I J).obj :=
    Functor.whiskerRight (HomotopyColimit.replacementComparison K I J)
      (ColimitFrame.resolutionFamily K I J).obj
  exact Functor.whiskerRight (NatTrans.op a)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft C (K ⥤ C) SSet.{max w v}).obj
      (fibrantTarget fib ⋙ (Functor.const K : C ⥤ K ⥤ C)))

lemma diagramSourceComparison_weakEquivalence [ModelCategory SSet.{max w v}]
    (hcof : cofibrations SSet.{max w v} = MorphismProperty.monomorphisms _)
    (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    weakEquivalences SSet.{max w v} (((diagramSourceComparison K I J fib).app F).app Y) := by
  let := Projective.modelCategory K I J
  have := constantTarget_isFibrant K I J fib Y
  let q := ColimitFrame.resolutionFamily K I J
  exact cosimplicialHomMap_weakEquivalence hcof
    (q.obj.map ((HomotopyColimit.replacementComparison K I J).app F.unop))
    (q.cofibrant ((HomotopyColimit.replacement K I J).obj F.unop)) (q.cofibrant F.unop)
    (q.map_weakEquivalence _
      (HomotopyColimit.replacementComparison_trivialFibration K I J F.unop).2) _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma left_weakEquivalence (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((left K I J cof fib).app F).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverFunctor.homLeft_weakEquivalence cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J)
    (ColimitFrame.augmentation K I J) hcof (ColimitFrame.augmentation_weakEquivalence K I J)
    F (fibrantTarget fib |>.obj Y)

include hcof in
lemma right_weakEquivalence (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((right K I J cof fib).app F).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverFunctor.homRight_weakEquivalence cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (ColimitFrame.frame K I J)
    (ColimitFrame.augmentation K I J) hcof (ColimitFrame.reedyCofibrant K I J)
    F (fibrantTarget fib |>.obj Y)

end SerrePositivity.DiagramModel.ColimitMapComparison
