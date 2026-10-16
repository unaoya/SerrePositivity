module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison

/-! # Actual all-center mixed squares and their commuting cubes -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram ResolutionArrowElementary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagram
variable (C : Type u) [Category.{v} C] [ModelCategory C]

structure Presentation where
  source : FramedResolution C
  middle : FramedResolution C
  target : ResolutionObject C
  final : ResolutionObject C
  pre : source ⟶ middle
  center : middle.inner.base ⟶ target.base
  post : target ⟶ final

variable (p : Presentation C)

abbrev a : ResolutionArrowDiagram.Index C := center p.middle p.target p.center
abbrev b : ResolutionArrowDiagram.Index C :=
  center p.source p.target (p.pre.map.base ≫ p.center)
abbrev c : ResolutionArrowDiagram.Index C :=
  center p.middle p.final (p.center ≫ p.post.base)
abbrev d : ResolutionArrowDiagram.Index C :=
  center p.source p.final (p.pre.map.base ≫ p.center ≫ p.post.base)
abbrev ab : a C p ⟶ b C p := pre p.source p.middle p.target p.pre p.center
abbrev ac : a C p ⟶ c C p := post p.middle p.target p.final p.center p.post
abbrev cd : c C p ⟶ d C p :=
  pre p.source p.middle p.final p.pre (p.center ≫ p.post.base)

/-- The real post map includes the reassociation of the final central base arrow. -/
def bd : b C p ⟶ d C p where
  hom := (𝟙 _, p.post)
  map_val := by
    change ((𝟙 _) ≫ (p.pre.map.base ≫ p.center)) ≫ p.post.base =
      p.pre.map.base ≫ p.center ≫ p.post.base
    rw [Category.id_comp, Category.assoc]

lemma commutes : ab C p ≫ bd C p = ac C p ≫ cd C p := by
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · change p.pre.op ≫ (𝟙 _) = (𝟙 _) ≫ p.pre.op
    rw [Category.id_comp, Category.comp_id]
  · change (𝟙 _) ≫ p.post = p.post ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]

/-- An object of the actual iterated arrow category, not merely four compatible base maps. -/
def square : Arrow (Arrow (ResolutionArrowDiagram.Index C)) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (ab C p)) (g := Arrow.mk (cd C p))
    (ac C p) (bd C p) (commutes C p).symm)

abbrev Index := InducedCategory (Arrow (Arrow (ResolutionArrowDiagram.Index C))) (square C)
abbrev forget : Index C ⥤ Arrow (Arrow (ResolutionArrowDiagram.Index C)) :=
  inducedFunctor (square C)
abbrev cornerA : Index C ⥤ ResolutionArrowDiagram.Index C :=
  forget C ⋙ Arrow.leftFunc ⋙ Arrow.leftFunc
abbrev cornerB : Index C ⥤ ResolutionArrowDiagram.Index C :=
  forget C ⋙ Arrow.leftFunc ⋙ Arrow.rightFunc
abbrev cornerC : Index C ⥤ ResolutionArrowDiagram.Index C :=
  forget C ⋙ Arrow.rightFunc ⋙ Arrow.leftFunc
abbrev cornerD : Index C ⥤ ResolutionArrowDiagram.Index C :=
  forget C ⋙ Arrow.rightFunc ⋙ Arrow.rightFunc

abbrev edgeAB : cornerA C ⟶ cornerB C :=
  Functor.whiskerLeft (forget C ⋙ Arrow.leftFunc) Arrow.leftToRight
abbrev edgeCD : cornerC C ⟶ cornerD C :=
  Functor.whiskerLeft (forget C ⋙ Arrow.rightFunc) Arrow.leftToRight
abbrev edgeAC : cornerA C ⟶ cornerC C :=
  Functor.whiskerRight (Functor.whiskerLeft (forget C) Arrow.leftToRight) Arrow.leftFunc
abbrev edgeBD : cornerB C ⟶ cornerD C :=
  Functor.whiskerRight (Functor.whiskerLeft (forget C) Arrow.leftToRight) Arrow.rightFunc

lemma edge_commutes : edgeAB C ≫ edgeBD C = edgeAC C ≫ edgeCD C := by
  apply NatTrans.ext
  funext p
  exact commutes C p

abbrev diagonal : cornerA C ⟶ cornerD C := edgeAB C ≫ edgeBD C
abbrev parameters := cornerA C ⋙ ResolutionArrowTupleCoherence.bigTuples C
abbrev vertexParameters := cornerA C ⋙ ResolutionArrowTupleCoherence.bigVertices C
abbrev smallValues := cornerD C ⋙ fibers C
abbrev vertexInclusion : vertexParameters C ⟶ parameters C :=
  Functor.whiskerLeft (cornerA C) (ResolutionArrowTupleCoherence.bigInclusion C)
abbrev vertexBoundary : vertexParameters C ⟶ NerveMovingParameter.lifted.{u} (smallValues C) :=
  Functor.whiskerLeft (cornerA C) (ResolutionArrowTupleCoherence.bigBoundary C) ≫
    Functor.whiskerRight (diagonal C) (NerveMovingParameter.lifted (fibers C))

lemma vertexInclusion_mono (p : Index C) : Mono ((vertexInclusion C).app p) :=
  ResolutionArrowTupleCoherence.bigInclusion_mono C (a C p)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagram
