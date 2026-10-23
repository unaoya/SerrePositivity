module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaColimitComparisonSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteConeIsoTransport

/-!
概要：実際の前層余極限の頂点関手が、元の非空有限極限全錐を保存すると証明する。
方針：元の共有比較辺・全脚の可換式から全錐の関手同型を作り、標準錐の極限性を移す。
規約：実際の指定余錐・元の全錐像を保持する。底の quasicategory 性は不要。
使われ方：P_Σ の sifted 余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op} (c : JoinCone p)

/-- 実際の有限錐像と標準有限評価余極限錐の、元の共有代表辺からの全関手同型。 -/
def sigmaColimitFiniteImageConeIso :
    FunctorIso (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift c)).val
      (sigmaPresheafColimitFiniteCone r c).val :=
  discreteConeIsoOfLegClasses
    (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift c))
    (sigmaPresheafColimitFiniteCone r c) (sigmaColimitApexComparisonEdge r q hq c)
    (sigmaColimitComponentComparisonEdge r q hq (p := p))
    (sigmaColimitComparisonLeg_commutes r q hq c)
    (sigmaColimitApexComparisonEdge_isInvertible r q hq c)
    (sigmaColimitComponentComparisonEdge_isInvertible r q hq (p := p))

include hq in
/-- 指定した元の前層余極限頂点関手は、元の非空有限極限全錐を保存する。 -/
lemma presheafColimitVertex_mapNonemptyCone_isLimit [IsSiftedInfinity B] (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift c)) :=
  IsLimitCone.of_functorIso (sigmaPresheafColimitFiniteCone_isLimit r c hc)
    (sigmaColimitFiniteImageConeIso r q hq c).symm

/-- 実際に供給済みの元の前層余極限の頂点関手は、元の非空有限極限全錐を保存する。 -/
lemma sigmaPresheafAmbientColimit_mapNonemptyCone_isLimit [IsSiftedInfinity B]
    (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (presheafCoconeVertexFunctor
      (presheafCoherentColimitCone (r ≫ sigmaPresheafInfinityInclusion C))) (JoinCone.ulift c)) :=
  presheafColimitVertex_mapNonemptyCone_isLimit r _
    (presheafCoherentColimitCone_evaluation_isColimit _) c hc

end SerrePositivity.InfinityCategories.HomotopyLimits
