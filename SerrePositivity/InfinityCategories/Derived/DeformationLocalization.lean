module
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.F1B.Localization
public import SerrePositivity.InfinityCategories.F1B.RestrictedPrecomposition
public import SerrePositivity.InfinityCategories.F1B.ReflectiveLocalization
/-!
概要：実ホモトピーによる分解–包含の比較から、局所化の全関手圏普遍性を得る。
方針：包含による制限を前合成の逆にし、指定辺を反転する関手族上で比較を可逆にする。
規約：局所化や反射随伴を仮定しない。使われ方：全 dg 加群の半自由出力分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
variable {X D : SSet.{u}} (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
/-- 局所化の候補の逆は、包含に沿う反転関手の制限。 -/
def deformationLocalizationRestriction (Y : SSet.{u}) :
    (invertingFunctors X Y W : SSet.{u}) ⟶ (ihom D).obj Y :=
  (invertingFunctors X Y W).ι ≫ (pre I).app Y
/-- 指定辺を成分に持つ全単体ホモトピーは、反転関手族上で可逆になる。 -/
def deformationLocalizationInvertingIso
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (Y : SSet.{u}) [Quasicategory Y] :
    FunctorIso ((invertingFunctors X Y W).ι ≫ (pre (L ≫ I)).app Y)
      (invertingFunctors X Y W).ι := by
  have e := functorIsoRestrictedPrecompositionOfHomotopy H
    (invertingFunctors X Y W).ι (by
      intro v f hf x
      have hv := fullSubcomplexOnVertices_vertex v
      change IsInvertingFunctorVertex X Y W v.val at hv
      unfold IsInvertingFunctorVertex at hv
      rw [show v.val = (functorVertexEquiv X Y) f from hf, Equiv.symm_apply_apply] at hv
      have hi := hv (hH x)
      exact (isInvertibleEdge_congr
        (e := (edgeOfSimplex (simplicialHomotopyVertexEdge H x).edge).map
          ((truncation 2).map f))
        (f := (simplicialHomotopyVertexEdge H x).toTruncated.map
          ((truncation 2).map f)) rfl).mp hi)
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using e
/-- 分解–包含の実比較は、任意の標的に対する前合成の同値を与える。 -/
def deformationLocalizationPrecompositionEquivalence
    (hL : InvertsEdges L W) (e : FunctorIso (I ≫ L) (𝟙 D))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (Y : SSet.{u}) [Quasicategory Y] :
    QCatEquivalence ((ihom D).obj Y) (invertingFunctors X Y W : SSet.{u}) where
  hom := localizationPrecomposition L W hL Y
  inv := deformationLocalizationRestriction I W Y
  homInvIso := by
    simpa only [deformationLocalizationRestriction, ← Category.assoc,
      localizationPrecomposition_ι, pre_map, NatTrans.comp_app,
      pre_id, NatTrans.id_app] using e.map_pre Y
  invHomIso := by
    let K := invertingFunctors X Y W
    let U := localizationPrecomposition L W hL Y
    let V := deformationLocalizationRestriction I W Y
    have h : FunctorIso ((V ≫ U) ≫ K.ι) ((𝟙 (K : SSet.{u})) ≫ K.ι) := by
      simpa only [V, U, K, deformationLocalizationRestriction, Category.assoc,
        localizationPrecomposition_ι, pre_map, NatTrans.comp_app, Category.id_comp] using
        deformationLocalizationInvertingIso L I W H hH Y
    let ff := fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u})
      ((ihom X).obj Y) (IsInvertingFunctorVertex X Y W)
    exact ff.preimageIso h
/-- 実変形比較と辺の反転から、局所化の普遍性を結論する。 -/
lemma isLocalization_of_deformation
    (hL : InvertsEdges L W) (e : FunctorIso (I ≫ L) (𝟙 D))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W) :
    IsLocalization L W := by
  refine ⟨hL, fun Y _ => ?_⟩
  exact (deformationLocalizationPrecompositionEquivalence L I W hL e H hH Y).isQCatEquivalence
/-- 局所化に沿う実前合成は、元の全関手 ∞ 圏への射として充満忠実。 -/
lemma IsLocalization.precomposition_isFullyFaithful {A B : SSet.{u}} {q : A ⟶ B}
    {V : Set (A _⦋1⦌)} (hq : IsLocalization q V) (Y : SSet.{u}) [Quasicategory Y] :
    IsFullyFaithful ((pre q).app Y) := by
  obtain ⟨hV, he⟩ := hq
  have hf := (he Y).isFullyFaithful
  have hi := isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom A).obj Y)
    (IsInvertingFunctorVertex A Y V)
  have hc := hf.comp hi
  change IsFullyFaithful
    (localizationPrecomposition q V hV Y ≫ (invertingFunctors A Y V).ι) at hc
  rw [localizationPrecomposition_ι] at hc
  exact hc
end SerrePositivity.InfinityCategories
