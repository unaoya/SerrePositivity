module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.PointSourceUniverse

/-!
概要：元の生成表示の一段への因子化から、同じ表示の入力付き全表示を構成する。
方針：元の一段の全 coslice 上で表示を制限し、右余錐頂点への制限を持ち上げる。
規約：元の余錐の全脚と入力図式を保持する。
使われ方：元の両成分表示を固定始域内の相対交互構成へ渡す。
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

/-- 概要：元の一段への因子化から、同じ生成表示の入力付き全表示が存在する。
方針：元の一点下添字の共終性と指定終点付き全余錐の持ち上げを使う。
規約：元の表示の全余錐脚を変更しない。
使われ方：compact 成分表示の入力付き正規化。 -/
lemma exists_nativeSourceNormalization_of_factorization
    {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {C K : SSet.{u + 1}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    {q : K ⟶ C} {w z : JoinCocone q} (i : I _⦋0⦌)
    (hw : w.vertex = D.app (Opposite.op ⦋0⦌) (ULift.up i))
    (k : (sliceUnder q).Edge w z)
    (hk : (k.map (sliceUnderProjection q)).edge =
      (Compact.coconeTransportLeg c (ULift.up i)).edge) :
    IsKappaFiltered μ (sliceUnder (SSet.yonedaEquiv.symm i)) ∧
      ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (sliceUnder (SSet.yonedaEquiv.symm i)) ⟶
          sliceUnder q,
        F ≫ sliceUnderProjection q =
          (SSet.uliftFunctor.{u + 1, u}).map
            (sliceUnderProjection (SSet.yonedaEquiv.symm i)) ≫ D ∧
        ∃ c' : JoinCocone F, IsColimitCone c' ∧ c'.vertex = z ∧
          c'.val ≫ sliceUnderProjection q =
            (c.restrict ((SSet.uliftFunctor.{u + 1, u}).map
              (sliceUnderProjection (SSet.yonedaEquiv.symm i)))).val := by
  have hfilter : IsKappaFiltered μ (sliceUnder (SSet.yonedaEquiv.symm i)) :=
    isKappaFiltered_sliceUnder hμ (isKappaSmall_of_finite hμ.aleph0_le _) _
  have := hfilter
  let b : (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I :=
    SSet.yonedaEquiv.symm (ULift.up i)
  let s := (pointCosliceUniverseIso.{u, u + 1} i).hom
  let V := sourceCosliceRestrictedCocone b s D c
  have hV : IsColimitCone V :=
    sourceCosliceRestrictedCocone_isColimit_of_rightCofinal hμ b s D c hc
      (pointCosliceUniverseProjection_isRightCofinal hμ i)
  have htip : joinInr K Δ[0] ≫ w.val = b ≫ D := by
    rw [SSet.yonedaEquiv_symm_comp]
    rw [← hw, JoinCocone.vertex_eq, Equiv.symm_apply_apply]
  have hv : V.vertex.val =
      (edgeCosliceVertex (k.map (sliceUnderProjection q)).toTruncated).val := by
    rw [sourceCosliceRestrictedCocone_vertex]
    change joinMap b (𝟙 Δ[0]) ≫ c.val =
      (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (k.map (sliceUnderProjection q)).edge
    rw [hk, Compact.coconeTransportLeg_edge]
    change joinMap b (𝟙 Δ[0]) ≫ c.val =
      (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
          joinMap (SSet.yonedaEquiv.symm (ULift.up i)) (𝟙 Δ[0]) ≫ c.val))
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  obtain ⟨F, hF, c', hc', hv', haug⟩ := exists_normalizedSourcePresentation_of_pointSource
    hμ k (b ≫ D) htip (s ≫ sliceUnderPostcomp b D) V hV hv
  refine ⟨hfilter, F, ?_, c', hc', hv', ?_⟩
  · calc
      _ = (s ≫ sliceUnderPostcomp b D) ≫ sliceUnderProjection (b ≫ D) := hF
      _ = (s ≫ sliceUnderProjection b) ≫ D := by
        rw [Category.assoc, sliceUnderPostcomp_projection, ← Category.assoc]
      _ = _ := by rw [pointCosliceUniverseIso_projection]
  · calc
      _ = V.val ≫ sliceUnderProjection (b ≫ D) := haug
      _ = (c.restrict (s ≫ sliceUnderProjection b)).val :=
        sourceCosliceRestrictedCocone_projection b s D c
      _ = _ := by
        change joinMap (s ≫ sliceUnderProjection b) (𝟙 Δ[0]) ≫ c.val = _
        rw [pointCosliceUniverseIso_projection]
        rfl

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
