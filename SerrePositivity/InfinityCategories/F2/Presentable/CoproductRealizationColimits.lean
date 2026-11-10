module

public import SerrePositivity.InfinityCategories.F2.Presentable.SimplicialBarIndex
public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitFromLocalLeftKan
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationUlift
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation

/-!
概要：小余積と小さい幾何学的実現から全小余極限を構成する。
方針：任意の全図式を全単体へ展開し、次数ごとの小余積とその実現を合成する。
規約：元の任意の小さい単体集合形状を扱い、追加の局所化存在を仮定しない。
使われ方：P_Σ 専用反映のための余完備性の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小余積と小さい幾何学的実現を持つ圏では、元の任意の小さい全図式が余極限を持つ。
方針：全単体の次数射影に沿う局所余極限を小余積で構成し、その実現から元の図式へ戻す。
規約：元の形状の quasicategory 性や標的の全小余極限を仮定しない。
使われ方：P_Σ 専用反映と小余極限保存の判定。 -/
lemma hasSmallColimits_of_coproducts_geometricRealizations
    {X : SSet.{u + 1}} [Quasicategory X]
    (hcop : HasSmallCoproducts X) (hgeom : HasSmallGeometricRealizations X) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X := by
  intro K F
  let Y := simplicialBarSimplexFamily K
  let j := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap K)
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (simplicialBarIndexNerveIso K)
  let F' := e.hom ≫ (j ≫ F)
  have hx : HasColimit F' := hasColimit_of_localLeftKan_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F'
    (elementsCoproduct_leftKanDiagram_hasColimit Y hcop F') hgeom
  have hj : IsFullyFaithful ((pre j).app X) :=
    localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} K) X
  have he : IsFullyFaithful ((pre e.hom).app X) :=
    ((isPrecompositionEquivalence_of_iso e) X).isFullyFaithful
  exact hasColimit_of_fullyFaithfulPrecomposition j hj F
    (hasColimit_of_fullyFaithfulPrecomposition e.hom he (j ≫ F) hx)

/-- 概要：全小余極限の存在は、小余積と小さい幾何学的実現の存在と同値。
方針：構成した十分条件と二種類の形状への制限を組み合わせる。
規約：元の標的と同じ宇宙に関する同値である。
使われ方：小余極限存在の公開判定。 -/
lemma hasSmallColimits_iff_coproducts_geometricRealizations
    {X : SSet.{u + 1}} [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X ↔ HasSmallCoproducts X ∧ HasSmallGeometricRealizations X :=
  ⟨fun h ↦ ⟨h.hasSmallCoproducts, h.hasSmallGeometricRealizations⟩,
    fun h ↦ hasSmallColimits_of_coproducts_geometricRealizations h.1 h.2⟩

end SerrePositivity.InfinityCategories.F2.Presentable
