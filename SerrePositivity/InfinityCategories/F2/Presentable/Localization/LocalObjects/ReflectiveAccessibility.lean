module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleFamilySaturationModels
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleReflectiveImage
public import SerrePositivity.InfinityCategories.F2.Presentable.ReflectionSmallColimits
public import SerrePositivity.InfinityCategories.F1.Universe.EquivalenceDescent

/-!
概要：一般の元の accessible 圏の反射的全部分圏に小さい compact 生成表示を構成する。
方針：反射した生成族の周囲での同型飽和を縮小し、その同じ模型を全部分圏へ持ち上げる。
規約：元の全部分圏に固定頂点写像の厳密な小ささを要求しない。
使われ方：局所対象圏の条件付き反射からの accessibility。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
open HomotopyLimits

/-- 概要：filtered 保存の反射的包含を持つ全部分圏は同じ濃度で accessible。
方針：周囲の小さい生成族を反射し、その同型飽和の小模型へ全生成表示を移す。
規約：全部分圏の元の単体集合を使用し、accessibility 自体を入力にしない。
使われ方：条件付き局所置換反射からの局所対象圏の生成表示。 -/
lemma reflectiveSubcategory_isKappaAccessible {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {P : C _⦋0⦌ → Prop}
    (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y))
    (r : ReflectiveSubcategory C P) (hC : IsKappaAccessible κ C)
    (hcol : HasSmallColimits C)
    (hR : IsKappaAccessibleFunctor κ (fullSubcomplexOnVertices C P).ι) :
    IsKappaAccessible κ (fullSubcomplexOnVertices C P : SSet.{u + 1}) := by
  let R := (fullSubcomplexOnVertices C P).ι
  let L := r.reflector
  have hff : IsFullyFaithful R := r.inclusion_fullyFaithful
  obtain ⟨hκ, _, A, hA, i, hi⟩ := hC
  have := hA
  let v : A _⦋0⦌ → C _⦋0⦌ := fun t ↦ R.app _ (L.app _ (i.app _ (ULift.up t)))
  have hacc : IsAccessible C :=
    ⟨κ, hκ, hcol.hasSmallKappaFilteredColimits κ, A, hA, i, hi⟩
  obtain ⟨B, hB, ⟨e⟩⟩ := hacc.exists_smallFamilySaturationModel v
  have := hB
  have hv : ∀ z, FamilySaturation v z → P z := by
    rintro z ⟨t, ⟨hz⟩⟩
    exact (hP hz).mpr (r.localization_mem (i.app _ (ULift.up t)))
  let j := e.hom ≫ familySaturationInclusion v
  let jD := fullSubcomplexLift P j (fun b ↦ hv _
    (fullSubcomplexOnVertices_vertex (e.hom.app _ b)))
  have hj : jD ≫ R = j := fullSubcomplexLift_ι _ _ _
  have hjff : IsFullyFaithful jD := by
    apply hff.cancel_right
    rw [hj]
    exact e.isQCatEquivalence.isFullyFaithful.comp
      (isFullyFaithful_fullSubcomplexOnVertices_ι C (FamilySaturation v))
  have hdcol := reflectiveSubcategory_hasSmallColimits r hcol
  refine ⟨hκ, hdcol.hasSmallKappaFilteredColimits κ, B, hB, jD, hjff, ?_, ?_⟩
  · intro b
    obtain ⟨t, ⟨ht⟩⟩ := fullSubcomplexOnVertices_vertex (e.hom.app _ (ULift.up b))
    have ht' : VertexIso (R.app _ (jD.app _ (ULift.up b)))
        (R.app _ (L.app _ (i.app _ (ULift.up t)))) := ht
    exact (Compact.isKappaCompact_iff_of_iso (hff.preimageVertexIso ht')).mpr
      (adjunction_isKappaCompact_image r.adjunction hR (hi.compact t))
  · intro x
    obtain ⟨K, hK, hκK, a, c, hc, hpres⟩ := hi.presentation (R.app _ x)
    have := hK
    have := hκK
    let G := ((SSet.uliftFunctor.{u + 1, u}).map a ≫ i) ≫ L
    let d := mapJoinCocone L c
    have hd : IsColimitCone d := mapJoinCocone_isColimit_of_adjunction r.adjunction c hpres
    have hdv : d.vertex = L.app _ (R.app _ x) := by
      rw [Ind.mapJoinCocone_vertex, hc]
    obtain ⟨d', hd', hv'⟩ := exists_colimitCone_vertex_of_iso d hd
      (eqToIso (congrArg HomotopyCategory.mk hdv) ≪≫ r.counitIso.app x)
    let H := fullSubcomplexLift (FamilySaturation v) (G ≫ R) (by
      rintro ⟨k⟩
      exact ⟨a.app _ k, ⟨Iso.refl _⟩⟩)
    let b := uliftMorphismDown (H ≫ e.inv)
    have hb : (SSet.uliftFunctor.{u + 1, u}).map b = H ≫ e.inv := uliftMorphismDown_lift _
    have he : FunctorIso
        (((SSet.uliftFunctor.{u + 1, u}).map b ≫ jD) ≫ R) (G ≫ R) := by
      rw [Category.assoc, hj, hb]
      have hh := (e.invHomIso.precomp H).postcomp (familySaturationInclusion v)
      simpa only [j, Category.assoc, Category.id_comp, H,
        familySaturationInclusion, fullSubcomplexLift_ι] using hh
    have heD := hff.preimageFunctorIso he
    obtain ⟨d'', hd'', hv''⟩ := exists_colimitCocone_functorIso_sameVertex heD.symm d' hd'
    exact ⟨K, hK, hκK, b, d'', hv''.trans hv', hd''⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
