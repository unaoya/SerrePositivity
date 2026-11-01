module

public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfMixedHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.EnrichedAdjunctionHomComposition

/-!
概要：元の LX→R_D(LX) の随伴像から cf 対応圏の左持ち上げ候補辺を構成する。
方針：同じ fibrant 置換を使い、豊穣合成互換から実際の前合成を元の Hom と照合。
規約：coCartesian 性は未主張。使われ方：HTT 5.2.4.6 の左持ち上げ条件の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] (R : EnrichedFunctor SSet.{u} D C)
variable [ModelCategory C] [ModelCategory D]
open SerrePositivity.KST.SConstruction SerrePositivity.HomotopyFunctionComplex
variable {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
variable [SerrePositivity.Quillen.IsLeftQuillen L]
variable (fibD : MorphismProperty.FunctorialFactorizationData
  (trivialCofibrations D) (fibrations D))

/-- 元の置換で得る、対応圏の持ち上げ候補の cf 対象。 -/
def quillenCfLeftLiftObject (X : CofibrantFibrantObjects C) : CofibrantFibrantObjects D :=
  ⟨(fibrantTarget fibD).obj (L.obj X.obj),
    quillenLeftReplacement_isCofibrant adj fibD X.obj, fibrantTarget_isFibrant fibD _⟩

/-- 元の置換比較の混合射としての像そのもの。 -/
def quillenCfLeftLiftArrow (X : CofibrantFibrantObjects C) :
    (quillenCfCollageBottom R).obj X ⟶
      (quillenCfCollageTop R).obj (quillenCfLeftLiftObject R adj fibD X) :=
  (quillenCfMixedHomEquiv R X _).symm
    (adj.homEquiv X.obj _ ((fibrantTargetComparison fibD).app (L.obj X.obj)))

/-- 混合射から元の通常の射を回収すると元の置換比較に一致。 -/
lemma quillenCfLeftLiftArrow_original (X : CofibrantFibrantObjects C) :
    quillenCfMixedHomEquiv R X _ (quillenCfLeftLiftArrow R adj fibD X) =
      adj.homEquiv X.obj _ ((fibrantTargetComparison fibD).app (L.obj X.obj)) :=
  (quillenCfMixedHomEquiv R X _).apply_symm_apply _

/-- 元の置換比較の混合射が定める、対応圏の coherent な候補辺。 -/
def quillenCfLeftLiftEdge (X : CofibrantFibrantObjects C) :
    (QuillenCfCollageInfinity R).Edge
      (coherentNerveVertex ((quillenCfCollageBottom R).obj X))
      (coherentNerveVertex ((quillenCfCollageTop R).obj (quillenCfLeftLiftObject R adj fibD X))) :=
  coherentNerveEdge (quillenCfLeftLiftArrow R adj fibD X)

/-- 同じ候補辺は標準区間の零から一への辺の上にある。 -/
lemma quillenCfLeftLiftEdge_projection (X : CofibrantFibrantObjects C) :
    (quillenCfCollageProjection R).app (Opposite.op ⦋1⦌)
      (quillenCfLeftLiftEdge R adj fibD X).edge =
        (homotopyIntervalEdge.{max u v}).edge :=
  quillenCfMixedEdge_projection R X _ _


variable (e : EnrichedAdjunctionHomComposition R adj)

/-- 候補辺による実際の前合成を、元の置換比較と随伴 Hom 同型の合成で表す。 -/
lemma quillenCfLeftLiftHom_comparison (X : CofibrantFibrantObjects C)
    (Y : CofibrantFibrantObjects D) :
    eHomWhiskerRight SSet (quillenCfLeftLiftArrow R adj fibD X)
        ((quillenCfCollageTop R).obj Y) =
      eHomWhiskerRight SSet ((fibrantTargetComparison fibD).app (L.obj X.obj)) Y.obj ≫
        (e.homIso X.obj Y.obj).hom := by
  dsimp only [quillenCfLeftLiftArrow]
  rw [quillenCfMixedHomWhiskerRight]
  exact (enrichedAdjunctionHom_precompose R adj e X.obj _ Y.obj _).symm


variable (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SD.tensor]
include e SD in
/-- 同じ候補辺による写像空間の合成は、固定 SM7 により trivial Kan fibration。 -/
lemma quillenCfLeftLiftHom_trivialKanFibration (X : CofibrantFibrantObjects C)
    (Y : CofibrantFibrantObjects D) :
    TrivialKanFibration (eHomWhiskerRight SSet (quillenCfLeftLiftArrow R adj fibD X)
      ((quillenCfCollageTop R).obj Y)) := by
  rw [quillenCfLeftLiftHom_comparison R adj fibD e]
  have hf := quillenLeftReplacementHom_trivialKanFibration (L := L) fibD SD X.obj Y.obj
  have hi : TrivialKanFibration (e.homIso X.obj Y.obj).hom := inferInstance
  exact ⟨MorphismProperty.comp_mem _ _ _ hf.mem hi.mem⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
