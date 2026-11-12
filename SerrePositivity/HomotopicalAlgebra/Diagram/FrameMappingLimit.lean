module

public import SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseMappingComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitMapComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.MappingLimit

/-! # The evaluated projective frame mapping diagram and its ordinary limit

The repackaged diagram is identified naturally with direct pointwise Hom.
The actual diagram-resolution Hom is its ordinary limit after the explicit
universe lift. Homotopy-limit computation is a separate remaining step.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.FrameMappingLimit
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev evaluatedHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{v} :=
  (EvaluatedFrame.family K I J).op ⋙ Functor.opHom K (SimplexCategory ⥤ C) ⋙
    (Functor.whiskeringRight Kᵒᵖ (SimplexCategory ⥤ C)ᵒᵖ (C ⥤ SSet.{v})).obj
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib)) ⋙
      flipFunctor Kᵒᵖ C SSet.{v}

def evaluatedHomIso : PointwiseMappingComparison.frameDiagram K I J fib ≅
    evaluatedHom K I J fib :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro k l f
      ext n h
      simp [PointwiseMappingComparison.frameDiagram, PointwiseMappingComparison.diagrams,
        evaluatedHom, FrameOverFunctor.hom, EvaluatedFrame.frame, EvaluatedFrame.family,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap])) (by
      intro Y Z f
      ext k n h
      rfl)) (by
    intro F G f
    ext Y k n h
    simp [PointwiseMappingComparison.frameDiagram, PointwiseMappingComparison.diagrams,
      evaluatedHom, FrameOverFunctor.hom, EvaluatedFrame.frame, EvaluatedFrame.family,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap])

@[simp]
lemma evaluatedHom_obj (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    ((evaluatedHom K I J fib).obj F).obj Y = MappingLimit.pointwise K
      ((ColimitFrame.diagramResolution K I J).obj F.unop) ((fibrantTarget fib).obj Y) := rfl

abbrev liftedFrameDiagram (F : (K ⥤ C)ᵒᵖ) (Y : C) : Kᵒᵖ ⥤ SSet.{max w v} :=
  ((PointwiseMappingComparison.frameDiagram K I J fib).obj F).obj Y ⋙ SSet.uliftFunctor.{w,v}

lemma hasLimit (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    HasLimit (liftedFrameDiagram K I J fib F Y) := by
  let A := (ColimitFrame.diagramResolution K I J).obj F.unop
  let Z := (fibrantTarget fib).obj Y
  let e : liftedFrameDiagram K I J fib F Y ≅ MappingLimit.lifted K A Z :=
    Functor.isoWhiskerRight (((evaluatedHomIso K I J fib).app F).app Y) SSet.uliftFunctor.{w,v}
  have := MappingLimit.hasLimit K A Z
  exact hasLimit_of_iso e.symm

/-- The actual diagram resolution Hom is the ordinary limit of exactly the
frame diagram that occurs in the pointwise RMap comparison cospan. -/
def diagramHomLimitIso (F : (K ⥤ C)ᵒᵖ) (Y : C)
    [HasLimit (liftedFrameDiagram K I J fib F Y)] :
    (((ColimitMapComparison.diagramHom K I J fib).obj F).obj Y) ≅
      limit (liftedFrameDiagram K I J fib F Y) := by
  let A := (ColimitFrame.diagramResolution K I J).obj F.unop
  let Z := (fibrantTarget fib).obj Y
  let e : liftedFrameDiagram K I J fib F Y ≅ MappingLimit.lifted K A Z :=
    Functor.isoWhiskerRight (((evaluatedHomIso K I J fib).app F).app Y) SSet.uliftFunctor.{w,v}
  have : HasLimit (MappingLimit.lifted K A Z) := MappingLimit.hasLimit K A Z
  exact MappingLimit.iso K A Z ≪≫ (HasLimit.isoOfNatIso e).symm

end SerrePositivity.DiagramModel.FrameMappingLimit
