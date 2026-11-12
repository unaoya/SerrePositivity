module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfMixedHom

/-!
概要：元の Q(RY)→RY から cf 対応圏の右持ち上げ候補辺を構成する。
方針：同じ cofibrant 置換と比較射を使い、混合 Hom の実際の後合成を照合。
規約：Cartesian 性は未主張。使われ方：HTT 5.2.4.6 の右持ち上げ条件の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] (R : EnrichedFunctor SSet.{u} D C)
variable [ModelCategory C] [ModelCategory D]
open _root_.SerrePositivity.KST.SConstruction _root_.SerrePositivity.HomotopyFunctionComplex
variable {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
variable [SerrePositivity.Quillen.IsLeftQuillen L]
variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

/-- 元の置換で得る、対応圏の持ち上げ候補の cf 対象。 -/
def quillenCfRightLiftObject (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C :=
  ⟨(cofibrantSource cofC).obj (R.obj Y.obj),
    cofibrantSource_isCofibrant cofC _, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenRightReplacement_isFibrant adj cofC Y.obj⟩

/-- 元の置換比較の混合射としての像そのもの。 -/
def quillenCfRightLiftArrow (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj (quillenCfRightLiftObject R adj cofC Y) ⟶
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y :=
  (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R _ Y).symm ((cofibrantSourceComparison cofC).app (R.obj Y.obj))

/-- 混合射から元の通常の射を回収すると元の置換比較に一致。 -/
lemma quillenCfRightLiftArrow_original (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R _ Y (quillenCfRightLiftArrow R adj cofC Y) =
      (cofibrantSourceComparison cofC).app (R.obj Y.obj) :=
  (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R _ Y).apply_symm_apply _

/-- 元の置換比較の混合射が定める、対応圏の coherent な候補辺。 -/
def quillenCfRightLiftEdge (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj (quillenCfRightLiftObject R adj cofC Y)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (quillenCfRightLiftArrow R adj cofC Y)

/-- 同じ候補辺は標準区間の零から一への辺の上にある。 -/
lemma quillenCfRightLiftEdge_projection (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R).app (Opposite.op ⦋1⦌)
      (quillenCfRightLiftEdge R adj cofC Y).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{max u v}).edge :=
  _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedEdge_projection R _ Y _


variable (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor]
include SC in
/-- 同じ候補辺による写像空間の合成は、固定 SM7 により trivial Kan fibration。 -/
lemma quillenCfRightLiftHom_trivialKanFibration (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)
    (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerLeft SSet ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X)
      (quillenCfRightLiftArrow R adj cofC Y)) := by
  dsimp only [quillenCfRightLiftArrow]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomWhiskerLeft]
  exact _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenRightReplacementHom_trivialKanFibration
    (R := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) cofC SC X.obj Y.obj

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
