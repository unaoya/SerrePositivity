module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonPrefixFactor
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedFaces
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegPostcomposition

/-!
概要：左側の比較余錐の全脚を、元の表示余錐の全後続制限へ戻す。
方針：等しい固定図式による移送は uncurry を保ち、公開済みの全脚の式を適用できる。
規約：ここでは HomotopyLimits の join 結合同型を使う。
使われ方：P-13 の結合同型比較を代入する直前の、全増大余錐の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 等しい固定図式の coslice 間の移送は、元の全 uncurry を変更しない。 -/
lemma sliceUnderUncurry_eqToIso {K X A : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (F : A ⟶ sliceUnder p) :
    sliceUnderUncurry (F ≫ (eqToIso (congrArg sliceUnder h)).hom) =
      sliceUnderUncurry F := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 左側比較余錐の脚の全二重展開は、元の表示余錐の後続全制限を回収する。 -/
lemma comparisonLeftCocone_leg_uncurry {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
    (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁)
    (j : (sliceUnder s.left_index) _⦋0⦌) :
    (HomotopyLimits.joinAssociator
        ((SSet.uliftFunctor.{u + 1, u}).obj s.left_shape) Δ[0] Δ[0]).hom ≫
      joinMap (𝟙 _) (joinStdSimplexIso 0 0).hom ≫
        sliceUnderUncurry (SSet.yonedaEquiv.symm
          (coconeTransportLeg (comparisonLeftCocone s) (ULift.up j)).edge) =
      joinMap (((uliftSliceUnderIso.{u, u + 1} s.left_index).hom).app _ (ULift.up j)).val
        (𝟙 Δ[0]) ≫ c₀.val := by
  dsimp only [comparisonLeftCocone]
  rw [coconeTransportLeg_post_edge]
  let V := sourceCosliceRestrictedCocone ((SSet.uliftFunctor.{u + 1, u}).map s.left_index)
    (uliftSliceUnderIso.{u, u + 1} s.left_index).hom D₀ c₀
  let e := eqToIso (congrArg sliceUnder s.left_diagram.symm)
  have he := SSet.yonedaEquiv_symm_comp (coconeTransportLeg V (ULift.up j)).edge e.hom
  change SSet.yonedaEquiv.symm (coconeTransportLeg V (ULift.up j)).edge ≫ e.hom =
    SSet.yonedaEquiv.symm ((coconeTransportLeg V (ULift.up j)).map e.hom).edge at he
  rw [← he, sliceUnderUncurry_eqToIso s.left_diagram.symm]
  exact sourceCosliceRestrictedCocone_leg_uncurry
    ((SSet.uliftFunctor.{u + 1, u}).map s.left_index)
    (uliftSliceUnderIso.{u, u + 1} s.left_index).hom D₀ c₀ (ULift.up j)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
