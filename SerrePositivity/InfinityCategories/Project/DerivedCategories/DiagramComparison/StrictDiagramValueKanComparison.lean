module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramValueFrameComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：同じ値frame比較を、全二変数のcoherentな空間値図式の同型へ運ぶ。
方針：添字の宇宙をAsSmallで揃え、同じ自然変換に既存の成分同値判定を適用する。
規約：通常endのホモトピー不変性は仮定しない。
使われ方：HTT 4.2.4.4のRR02、値の比較からcoherent係数への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance valueKanModel : ModelCategory (Complex A) := EInfinity.projectiveModelCategory A
local instance valueKanInitial : HasInitial (Complex A) :=
  (isZero_zero (Complex A)).isInitial.hasInitial

local instance valueKanFrameInitial : HasInitial (SimplexCategory ⥤ Complex A) :=
  (isZero_zero (SimplexCategory ⥤ Complex A)).isInitial.hasInitial

/-- 同じframeの二変数Homを、宇宙を揃えた積の添字で表示する。 -/
def strictDiagramFrameValueMatrix (P : strictDiagramIndex d ⥤ (SimplexCategory ⥤ Complex A))
    (Y : StrictComplexDiagram A d) :
    AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) ⥤ SSet.{u} :=
  AsSmall.down ⋙ Functor.uncurry.obj
    (FrameOverFunctor.hom P ⋙
      (Functor.whiskeringLeft (strictDiagramIndex d) (Complex A) SSet.{u}).obj
        (strictDiagramFibrantTarget A d Y))

/-- 指定frameのKan性で、同じ二変数の図式を束縛する。 -/
def strictDiagramFrameValueKanDiagram (P : strictDiagramIndex d ⥤ (SimplexCategory ⥤ Complex A))
    (hP : ∀ i, reedyLeft simplex (cofibrations (Complex A)) (initial.to (P.obj i)))
    (hc : ∀ i {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences (Complex A) ((P.obj i).map f))
    (Y : StrictComplexDiagram A d) :
    AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) ⥤ KanObject.{u} where
  obj t := ⟨(strictDiagramFrameValueMatrix A d P Y).obj t, by
    haveI := strictDiagramFibrantTarget_obj_isFibrant A d Y (AsSmall.down.obj t).2
    exact HomotopyFunctionComplex.cosimplicialHom_kanComplex _ (hP (AsSmall.down.obj t).1.unop)
      (hc (AsSmall.down.obj t).1.unop) _⟩
  map f := (strictDiagramFrameValueMatrix A d P Y).map f
  map_id t := (strictDiagramFrameValueMatrix A d P Y).map_id t
  map_comp f g := (strictDiagramFrameValueMatrix A d P Y).map_comp f g

/-- 元の評価frameの全二変数Homを、同じ射の作用でKan図式へ束縛する。 -/
def strictDiagramEvaluatedValueKan (X Y : StrictComplexDiagram A d) :
    AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) ⥤ KanObject.{u} :=
  strictDiagramFrameValueKanDiagram A d (strictDiagramEvaluatedSourceFrames A d X)
    (strictDiagramEvaluatedSourceFrame_cofibrant A d X)
    (strictDiagramEvaluatedSourceFrame_homotopicallyConstant A d X) Y

/-- 標準値frameの全二変数HomのKan図式。 -/
def strictDiagramStandardValueKan (X Y : StrictComplexDiagram A d) :
    AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) ⥤ KanObject.{u} :=
  strictDiagramFrameValueKanDiagram A d
    (X ⋙ (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)).obj)
    (fun i => (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)).cofibrant (X.obj i))
    (fun i => (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)).atObject
      (X.obj i) |>.homotopicallyConstant) Y

/-- 同じ共通frameの全二変数HomのKan図式。 -/
def strictDiagramCommonValueKan (X Y : StrictComplexDiagram A d) :
    AsSmall.{u} ((strictDiagramIndex d)ᵒᵖ × strictDiagramIndex d) ⥤ KanObject.{u} :=
  strictDiagramFrameValueKanDiagram A d (strictDiagramCommonValueFrame A d X)
    (FrameOverFunctor.commonObj_cofibrant (strictDiagramValueCofFactorization A)
      (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
      (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X))
    (FrameOverFunctor.commonObj_homotopicallyConstant (strictDiagramValueCofFactorization A)
      (cosimplicialResolutionFamily (strictDiagramValueCofFactorization A)) X
      (strictDiagramEvaluatedSourceFrames A d X) (strictDiagramEvaluatedAugmentation A d X)
      (strictDiagramEvaluatedAugmentation_weak A d X)) Y

/-- 左脚の同じ全自然変換を、宇宙を揃えた二変数へ移す。 -/
def strictDiagramValueKanLeft (X Y : StrictComplexDiagram A d) :
    strictDiagramStandardValueKan A d X Y ⋙ kanObjectForget ⟶
      strictDiagramCommonValueKan A d X Y ⋙ kanObjectForget :=
  Functor.whiskerLeft AsSmall.down (Functor.uncurry.map
    (Functor.whiskerRight (strictDiagramValueFrameHomLeft A d X)
      ((Functor.whiskeringLeft (strictDiagramIndex d) (Complex A) SSet.{u}).obj
        (strictDiagramFibrantTarget A d Y))))

/-- 右脚も同じ二変数の自然変換として宇宙を移す。 -/
def strictDiagramValueKanRight (X Y : StrictComplexDiagram A d) :
    strictDiagramEvaluatedValueKan A d X Y ⋙ kanObjectForget ⟶
      strictDiagramCommonValueKan A d X Y ⋙ kanObjectForget :=
  Functor.whiskerLeft AsSmall.down (Functor.uncurry.map
    (Functor.whiskerRight (strictDiagramValueFrameHomRight A d X)
      ((Functor.whiskeringLeft (strictDiagramIndex d) (Complex A) SSet.{u}).obj
        (strictDiagramFibrantTarget A d Y))))

/-- 標準frameから共通frameへの同じ比較は、全coherent図式の同型となる。 -/
def strictDiagramValueKanLeftIso (X Y : StrictComplexDiagram A d) :
    FunctorIso (kanDiagramCoherentNerve (strictDiagramStandardValueKan A d X Y))
      (kanDiagramCoherentNerve (strictDiagramCommonValueKan A d X Y)) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨strictDiagramStandardValueKan A d X Y, trivial⟩)
    (G := ⟨strictDiagramCommonValueKan A d X Y, trivial⟩)
    (strictDiagramValueKanLeft A d X Y)
    (fun t => by
      haveI := ((strictDiagramStandardValueKan A d X Y).obj t).isKanComplex
      haveI := ((strictDiagramCommonValueKan A d X Y).obj t).isKanComplex
      have h : IsSimplicialHomotopyEquivalence
          (X := ((strictDiagramStandardValueKan A d X Y).obj t).obj)
          (Y := ((strictDiagramCommonValueKan A d X Y).obj t).obj)
          ((strictDiagramValueKanLeft A d X Y).app t) :=
        strictDiagramValueFrameHomLeft_equivalence A d X Y
          (AsSmall.down.obj t).1 (AsSmall.down.obj t).2
      exact h.isQCatEquivalence)

/-- 評価frameから共通frameへの同じ比較も、全coherent図式の同型となる。 -/
def strictDiagramValueKanRightIso (X Y : StrictComplexDiagram A d) :
    FunctorIso (kanDiagramCoherentNerve (strictDiagramEvaluatedValueKan A d X Y))
      (kanDiagramCoherentNerve (strictDiagramCommonValueKan A d X Y)) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨strictDiagramEvaluatedValueKan A d X Y, trivial⟩)
    (G := ⟨strictDiagramCommonValueKan A d X Y, trivial⟩)
    (strictDiagramValueKanRight A d X Y)
    (fun t => by
      haveI := ((strictDiagramEvaluatedValueKan A d X Y).obj t).isKanComplex
      haveI := ((strictDiagramCommonValueKan A d X Y).obj t).isKanComplex
      have h : IsSimplicialHomotopyEquivalence
          (X := ((strictDiagramEvaluatedValueKan A d X Y).obj t).obj)
          (Y := ((strictDiagramCommonValueKan A d X Y).obj t).obj)
          ((strictDiagramValueKanRight A d X Y).app t) :=
        strictDiagramValueFrameHomRight_equivalence A d X Y
          (AsSmall.down.obj t).1 (AsSmall.down.obj t).2
      exact h.isQCatEquivalence)

/-- 同じ共通frameを介して、評価係数の全図式を標準係数へ比較する。 -/
def strictDiagramValueKanIso (X Y : StrictComplexDiagram A d) :
    FunctorIso (kanDiagramCoherentNerve (strictDiagramEvaluatedValueKan A d X Y))
      (kanDiagramCoherentNerve (strictDiagramStandardValueKan A d X Y)) :=
  strictDiagramValueKanRightIso A d X Y ≪≫ (strictDiagramValueKanLeftIso A d X Y).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
