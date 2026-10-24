module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaRepresentableCoproductInd
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaGeometricRealizations
public import SerrePositivity.InfinityCategories.F2.Presentable.SimplicialBarIndex
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullyFaithfulPrecompositionColimits
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationUlift
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation

/-!
概要：P_Σ 内の表現可能小図式の余極限の simplicial Ind 表示。
方針：全単体の次数射影に沿って小余積を作り、幾何学的実現で回収する。
規約：元の余極限余錐の頂点との同型と全単体的図式を保持する。
使われ方：反映した bar 表示による P_Σ の filtered・geometric 生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：表現可能小図式の指定余極限は、各項が Ind に属する単体的図式の実現である。
方針：全単体への展開を次数ごとに左 Kan 延長し、同じ全余極限を比較する。
規約：元の指定頂点を同型で回収し、次数ごとの存在だけに弱めない。
使われ方：任意の P_Σ 対象の simplicial Ind 表示。
-/
lemma sigma_smallDiagram_simplicialIndPresentation
    {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {K : SSet.{u}} (p : K ⟶ C)
    (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C))
    (hc : IsColimitCone c) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve SmallSimplexOpposite.{u}) ⟶
        SigmaPresheafInfinity C) (d : JoinCocone G),
      IsColimitCone d ∧ Nonempty (VertexIso d.vertex c.vertex) ∧
      ∀ n : SmallSimplexOpposite.{u}, Ind.IsIndVertex Cardinal.aleph0 C
        ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
          (G.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex n)))) := by
  let Y := simplicialBarSimplexFamily K
  let r := nerveMap (simplicialBarToTransport K) ≫ transportSimplexFirstVertexMap K
  let δ := nerveMap (Functor.Elements.π Y)
  obtain ⟨G, β, hβ⟩ := sigmaSmallRepresentable_exists_leftKanExtension hC δ (r ≫ p)
  let j := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap K)
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (simplicialBarIndexNerveIso K)
  have hj : IsFullyFaithful ((pre j).app (SigmaPresheafInfinity C)) :=
    localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} K) _
  have he : IsFullyFaithful ((pre e.hom).app (SigmaPresheafInfinity C)) :=
    ((isPrecompositionEquivalence_of_iso e) _).isFullyFaithful
  have hcj := (isColimitCone_iff_restrict_of_fullyFaithful_pre j hj c).mp hc
  have hce := (isColimitCone_iff_restrict_of_fullyFaithful_pre e.hom he (c.restrict j)).mp hcj
  have hdiag : e.hom ≫ (j ≫ ((SSet.uliftFunctor.{u + 1, u}).map p ≫
      sigmaYonedaInfinityMap C)) =
      (SSet.uliftFunctor.{u + 1, u}).map (r ≫ p) ≫ sigmaYonedaInfinityMap C := by
    simp only [e, j, r, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  let t := (c.restrict j).restrict e.hom
  let t' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ p) ≫ sigmaYonedaInfinityMap C) :=
    ⟨t.val, t.property.trans hdiag⟩
  have ht' := (F2.isColimitCone_iff_of_cocone_val_eq t t' rfl).mp hce
  obtain ⟨d, hd⟩ := sigma_hasSmallGeometricRealizations C G
  refine ⟨G, d, hd, ⟨leftKan_colimitVertexIso
    ((SSet.uliftFunctor.{u + 1, u}).map δ) β hβ t' ht' d hd⟩, ?_⟩
  intro n
  obtain ⟨a, ha, hv⟩ := hβ.colimitValue (ULift.up (nerveVertex n))
  have hr := (Ind.isColimitCone_iff_restrict_rightCofinal (elementsCoproductKanComparison Y n)
    (elementsCoproductKanComparison_isRightCofinal Y n) a).mp ha
  let p' := nerveMap (elementsDegreeFiber Y n ⋙ CostructuredArrow.proj _ n) ≫ r ≫ p
  have he' : elementsCoproductKanComparison Y n ≫
      leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ)
        ((SSet.uliftFunctor.{u + 1, u}).map (r ≫ p) ≫ sigmaYonedaInfinityMap C)
        (ULift.up (nerveVertex n)) =
      (SSet.uliftFunctor.{u + 1, u}).map p' ≫ sigmaYonedaInfinityMap C := by
    rw [leftKanDiagram, ← Category.assoc, elementsCoproductKanComparison_projection]
    simp only [p', Functor.map_comp, Category.assoc]
  let a' := a.restrict (elementsCoproductKanComparison Y n)
  let a'' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p' ≫ sigmaYonedaInfinityMap C) :=
    ⟨a'.val, a'.property.trans he'⟩
  have ha'' := (F2.isColimitCone_iff_of_cocone_val_eq a' a'' rfl).mp hr
  have hh := sigmaYoneda_smallCoproduct_isInd hC p' a'' ha''
  have hv' : a''.vertex = G.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex n)) := hv
  rwa [hv'] at hh

end SerrePositivity.InfinityCategories.F2.Presentable
