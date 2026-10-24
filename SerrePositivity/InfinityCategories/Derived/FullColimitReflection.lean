module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.DGNerve.FullInclusionExtension
public import SerrePositivity.InfinityCategories.Derived.CosliceBoundaryFromJoinFaces

/-! # 充満 dg 部分圏による余極限性の反映

概要：充満 dg 部分圏の錐が周囲の dg nerve で余極限なら、部分圏の内部でも余極限である。
方針：周囲で coslice 境界を充填し、境界の join が全頂点を覆うことから充填を部分圏へ持ち上げる。
規約：HTT §1.2.13、HA Construction 1.3.1.6。使われ方：標準 cofiber の余極限性の部分圏への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 概要：充満 dg 部分圏の錐を包含で周囲の dg nerve の錐へ送る。
方針：錐の写像を後合成し、左因子の固定条件を後合成する。
規約：HTT §1.2.13。使われ方：周囲での余極限性を述べる際の錐。 -/
def fullInclusionCocone {K : SSet.{max u v}} {p : K ⟶ dgNerve A (DGFullSubcategory D P)}
    (c : JoinCocone p) : JoinCocone (p ≫ dgNerve.map (dgFullSubcategoryInclusion A D P)) :=
  ⟨c.val ≫ dgNerve.map (dgFullSubcategoryInclusion A D P), by rw [← Category.assoc, c.property]⟩

/-- 概要：充満 dg 部分圏の錐の包含による像が余極限なら、元の錐も余極限である。
方針：周囲の coslice で得た充填の uncurry を全頂点を覆う境界に沿って持ち上げ、単射性で固定条件を戻す。
規約：HTT §1.2.13、HA Construction 1.3.1.6。使われ方：cofiber で閉じた部分圏の引き戻しの構成。 -/
lemma isColimitCone_of_fullInclusion {K : SSet.{max u v}}
    {p : K ⟶ dgNerve A (DGFullSubcategory D P)} (c : JoinCocone p)
    (hc : IsColimitCone (fullInclusionCocone A D P c)) : IsColimitCone c := by
  intro n b hb
  let q := dgNerve.map (dgFullSubcategoryInclusion A D P)
  let b' := b ≫ sliceUnderPostcomp p q
  have hb' : boundaryVertex n 0 ≫ b' =
      SSet.yonedaEquiv.symm (fullInclusionCocone A D P c) := by
    dsimp only [b']
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hc n b' hb'
  have hboundary : joinMap (𝟙 K) (SSet.boundary (n + 1)).ι ≫ sliceUnderUncurry F =
      sliceUnderUncurry b ≫ q := by
    rw [← sliceUnderUncurry_precomp, hF]
    exact sliceUnderUncurry_postcomp b q
  obtain ⟨L, hLboundary, hLimage⟩ := fullInclusion_extension A D P _
    (joinMap_vertices_surjective _ _ (fun z => ⟨z, rfl⟩) (boundary_vertices_surjective n))
    (sliceUnderUncurry b) (sliceUnderUncurry F) hboundary
  have hfixed : joinInl K (Δ[n + 1] : SSet.{max u v}) ≫ L = p := by
    apply (cancel_mono q).1
    rw [Category.assoc, hLimage]
    exact sliceUnderUncurry_fixed F
  refine ⟨sliceUnderCurry L hfixed, ?_⟩
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
  exact hLboundary

end SerrePositivity.InfinityCategories.DGNerve
