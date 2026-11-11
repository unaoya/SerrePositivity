module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardFiberPushout
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-! # D(S) の安定性

概要：任意の四角形の押し出し性と引き戻し性が同値であり、D(S) は安定である。
方針：同じ span/cospan の標準双カルテジアン四角形と比較し、全図式の同型で普遍性を移す。
規約：三角構造と安定性を仮定しない。使われ方：D7 の三角比較、β3〜β5 の対象供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- D(S) の任意の押し出し四角形は引き戻しでもある。 -/
lemma derived_isPullbackSquare_of_isPushoutSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F := by
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone G
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_span (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_isPushout _
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone_isColimit _ _ hF
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso c d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c d hc hd)).precomp
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ G))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ F)) at e
  simp only [Iso.inv_hom_id_assoc] at e
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPullbackSquare.of_functorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare_isPullback _) e

/-- D(S) の任意の引き戻し四角形は押し出しでもある。 -/
lemma derived_isPushoutSquare_of_isPullbackSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedCospanFiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone G
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedCospanFiberSquare_cospan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedCospanFiberSquare_isPullback _
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone_isLimit _ _ hF
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso c d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso c d hc hd)).precomp
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ G))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ F)) at e
  simp only [Iso.inv_hom_id_assoc] at e
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPushoutSquare.of_functorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedCospanFiberSquare_isPushout _) e

/-- 任意の D(S) の四角形について押し出し性と引き戻し性は同値。 -/
theorem derived_isPullbackSquare_iff_isPushoutSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F :=
  ⟨derived_isPushoutSquare_of_isPullbackSquare F, derived_isPullbackSquare_of_isPushoutSquare F⟩

/-- 任意の可換環上の非有界導来 ∞ 圏は安定である。 -/
instance derivedInfinityCategory_isStable (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) where
  toHasZeroVertex := inferInstance
  fiber_exists := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory_fiber_exists
  cofiber_exists := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory_cofiber_exists
  fiber_iff_cofiber t := derived_isPullbackSquare_iff_isPushoutSquare t.square

end SerrePositivity.InfinityCategories.Project.DerivedCategories
