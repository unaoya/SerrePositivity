module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CosliceIndRelativeFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.SmallPrefixCofinality
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedVertex

/-!
概要：固定始域の下の Ind 表示内で、全前置図式を固定する相対因子化を作る。
方針：前置添字の全 coslice の共終性から同じ底の余極限を回収する。
規約：表示添字と元の指定余錐を変更しない。
使われ方：長さ κ₀ の相対交互構成の後続段と極限前置段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：元の Ind 表示の一段で、小さい全前置図式と全余錐を厳密に保持して因子化する。
方針：前置添字の coslice を共終な表示として使い、相対 compact 因子化へ渡す。
規約：前置図式に終頂点を要求せず、元の表示脚の全制限を返す。
使われ方：共通 κ₀ の表示添字内の相対交互構成の一段。 -/
lemma compactDiagram_factorization_over_smallPrefixPresentation_coslice_ind
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {J K I B S : SSet.{u}} [Quasicategory S] [Quasicategory J] [Quasicategory K]
    [Quasicategory I] [Quasicategory B] [IsKappaFiltered μ I]
    (hS : IsKappaSmall μ S)
    (s₀ : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ Ind.IndInfinity μ B)
    (hs₀ : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (s₀.app (Opposite.op ⦋0⦌) v))
    (hJ : IsKappaSmall μ J) (hK : IsKappaSmall μ K) (a : K ⟶ I)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder s₀)
    (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone (sliceUnderProjection s₀) c))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ sliceUnder s₀)
    (hQ : ∀ j, Compact.IsKappaCompact.{u, u + 1} μ
      ((q ≫ sliceUnderProjection s₀).app (Opposite.op ⦋0⦌) j))
    (i : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj J) [Mono i]
    (hp : i ≫ q = (SSet.uliftFunctor.{u + 1, u}).map a ≫ D)
    (z : JoinCocone q)
    (hz : (z.restrict i).val =
      (c.restrict ((SSet.uliftFunctor.{u + 1, u}).map a)).val) :
    let b := (SSet.uliftFunctor.{u + 1, u}).map a
    let s := (uliftSliceUnderIso.{u, u + 1} a).hom
    let e := eqToIso (congrArg sliceUnder hp.symm)
    let F := s ≫ sliceUnderPostcomp b D ≫ e.hom
    let v := mapJoinCocone e.hom (sourceCosliceRestrictedCocone b s D c)
    ∃ j : (sliceUnder a) _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = F.app _ (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge =
          (Compact.coconeTransportLeg v (ULift.up j)).edge := by
  let b := (SSet.uliftFunctor.{u + 1, u}).map a
  let s := (uliftSliceUnderIso.{u, u + 1} a).hom
  let e := eqToIso (congrArg sliceUnder hp.symm)
  let v₀ := sourceCosliceRestrictedCocone b s D c
  let F := s ≫ sliceUnderPostcomp b D ≫ e.hom
  let v := mapJoinCocone e.hom v₀
  have : IsKappaFiltered μ (sliceUnder a) := isKappaFiltered_sliceUnder Fact.out hK a
  have hs : IsRightCofinal (s ≫ sliceUnderProjection b) := by
    dsimp only [s, b]
    rw [uliftSliceUnderIso_projection]
    exact Ind.isRightCofinal_ulift _ (smallPrefix_cosliceProjection_isRightCofinal Fact.out hK a)
  have hep {T X : SSet.{u + 1}} {f g : T ⟶ X} (h : f = g) :
      (eqToIso (congrArg sliceUnder h)).hom ≫ sliceUnderProjection g =
        sliceUnderProjection f := by
    subst g
    rfl
  have hval : (mapJoinCocone (sliceUnderProjection (i ≫ q)) v).val =
      (c.restrict (s ≫ sliceUnderProjection b)).val := by
    calc
      _ = (mapJoinCocone (sliceUnderProjection (b ≫ D)) v₀).val := by
        change (v₀.val ≫ e.hom) ≫ sliceUnderProjection (i ≫ q) =
          v₀.val ≫ sliceUnderProjection (b ≫ D)
        exact (Category.assoc _ _ _).trans (congrArg (fun g ↦ v₀.val ≫ g) (hep hp.symm))
      _ = _ := sourceCosliceRestrictedCocone_projection b s D c
  have hv : IsColimitCone (mapJoinCocone
      (sliceUnderProjection (i ≫ q) ≫ sliceUnderProjection s₀) v) := by
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr
      ((Ind.isColimitCone_iff_restrict_rightCofinal _ hs
        (mapJoinCocone (sliceUnderProjection s₀) c)).mp hc)
    change v.val ≫ (sliceUnderProjection (i ≫ q) ≫ sliceUnderProjection s₀) =
      joinMap (s ≫ sliceUnderProjection b) (𝟙 Δ[0]) ≫ (c.val ≫ sliceUnderProjection s₀)
    have hval' : v.val ≫ sliceUnderProjection (i ≫ q) =
        joinMap (s ≫ sliceUnderProjection b) (𝟙 Δ[0]) ≫ c.val := hval
    rw [← Category.assoc, hval', Category.assoc]
  have hzv : z.restrict i = v.vertex := by
    apply Subtype.ext
    have hvraw : v.vertex.val = (c.restrict b).val := by
      change (e.hom.app (Opposite.op ⦋0⦌) v₀.vertex).val = (c.restrict b).val
      rw [Ind.sliceUnder_eqToIso_val hp.symm, sourceCosliceRestrictedCocone_vertex]
    exact hz.trans hvraw.symm
  exact compactDiagram_factorization_relative_coslice_ind hμ hS hJ hK s₀ hs₀ q hQ i F v hv z hzv

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
