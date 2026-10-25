module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeNestedCosliceProjection
public import SerrePositivity.InfinityCategories.Stable.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapIso
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CoslicePinchedLeft

/-!
概要：固定辺全体の coslice を、元の始点の coslice 内の同じ辺の下の coslice と同定する。
方針：二点の join の標準同型と反復 coslice の同型を合成し、始点制限を保持する。
規約：元の辺と元の始点を厳密に保持する。
使われ方：HTT 5.5.5.12 の写像空間を前合成の fiber として読む工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}} {a b : C _⦋0⦌} (f : C.Edge a b)

/-- 元の辺全体の coslice と、始点の下の同じ辺の coslice の厳密な同型。 -/
def edgeCosliceUnderIso :
    sliceUnder (SSet.yonedaEquiv.symm f.edge) ≅
      sliceUnder (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated)) :=
  sliceUnderReindexIso (joinStdSimplexIso 0 0) (SSet.yonedaEquiv.symm f.edge) ≪≫
    nestedCosliceIso (edgeCosliceVertex f.toTruncated)

/-- 元の辺の始点を、同じ元の点図式に揃えた制限。 -/
def edgeCosliceSourceRestriction :
    sliceUnder (SSet.yonedaEquiv.symm f.edge) ⟶ sliceUnder (SSet.yonedaEquiv.symm a) :=
  normalizedCoconeRestriction (SSet.yonedaEquiv.symm f.edge) (stdSimplex.δ (1 : Fin 2))
    (by
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact f.src_eq)

/-- 反復 coslice の同型は、元の始点への全制限を保持する。 -/
lemma edgeCosliceUnderIso_projection :
    (edgeCosliceUnderIso f).hom ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated)) =
      edgeCosliceSourceRestriction f := by
  change (sliceUnderReindexIso (joinStdSimplexIso 0 0)
      (SSet.yonedaEquiv.symm f.edge)).hom ≫
        colimitCosliceRestriction (edgeCosliceVertex f.toTruncated) = _
  apply sliceUnderUncurry_injective
  rw [colimitCosliceRestriction_uncurry (p := SSet.yonedaEquiv.symm a)
      (edgeCosliceVertex f.toTruncated)]
  change _ = sliceUnderUncurry ((𝟙 _) ≫ edgeCosliceSourceRestriction f)
  rw [edgeCosliceSourceRestriction, normalizedCoconeRestriction_uncurry]
  have h : sliceUnderUncurry ((sliceUnderReindexIso (joinStdSimplexIso 0 0)
      (SSet.yonedaEquiv.symm f.edge)).hom) =
      joinMap (joinStdSimplexIso 0 0).hom (𝟙 _) ≫
        sliceUnderUncurry (𝟙 (sliceUnder (SSet.yonedaEquiv.symm f.edge))) := by
    exact sliceUnderUncurry_restrict (𝟙 _) (joinStdSimplexIso 0 0).hom
  rw [h, ← Category.assoc, ← joinMap_comp, Category.id_comp, joinStdSimplexIso_zero_inl]

/-- 始点制限の同じ指定 fiber は、始点の coslice 内の全左写像空間そのもの。 -/
def edgeCosliceSourceFiberIso (g : (sliceUnder (SSet.yonedaEquiv.symm a)) _⦋0⦌) :
    vertexFiber (edgeCosliceSourceRestriction f) g ≅
      pinchedHomLeft (edgeCosliceVertex f.toTruncated) g :=
  asIso (vertexFiberMap (edgeCosliceSourceRestriction f)
    (sliceUnderProjection (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated)))
    (edgeCosliceUnderIso f).hom (edgeCosliceUnderIso_projection f) g) ≪≫
      (pinchedLeftCosliceFiberIso (edgeCosliceVertex f.toTruncated) g).symm

/-- 同じ fiber の同型は元の反復 coslice への射を保持する。 -/
lemma edgeCosliceSourceFiberIso_hom_ι
    (g : (sliceUnder (SSet.yonedaEquiv.symm a)) _⦋0⦌) :
    (edgeCosliceSourceFiberIso f g).hom ≫
        (pinchedLeftCosliceFiberIso (edgeCosliceVertex f.toTruncated) g).hom ≫
          vertexFiberι
            (sliceUnderProjection (SSet.yonedaEquiv.symm (edgeCosliceVertex f.toTruncated))) g =
      vertexFiberι (edgeCosliceSourceRestriction f) g ≫ (edgeCosliceUnderIso f).hom := by
  simp only [edgeCosliceSourceFiberIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact vertexFiberMap_ι _ _ _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
