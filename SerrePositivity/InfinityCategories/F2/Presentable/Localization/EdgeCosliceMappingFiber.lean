module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EdgeCosliceSourceComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalEdgeRestriction

/-!
概要：coslice 内の写像空間を、元の固定終点の始点制限の同じ fiber と同定する。
方針：底上の比較の二重 fiber と反復 coslice の同型を合成する。
規約：元の指定辺・指定終点・指定余錐を保持する。
使われ方：HTT 5.5.5.12 と局所性の全写像空間による判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {a b : C _⦋0⦌} (f : C.Edge a b)

/-- 正規化した始点制限は、元の可変終点を厳密に保持する。 -/
lemma edgeCosliceSourceRestriction_projection :
    edgeCosliceSourceRestriction f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm a) =
      sliceUnderProjection (SSet.yonedaEquiv.symm f.edge) :=
  normalizedCoconeRestriction_projection _ _ _

/-- 元の固定終点上の始点制限。 -/
def edgeCosliceSourceMapping (y : C _⦋0⦌) :
    coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y ⟶
      coconeMappingSpace (SSet.yonedaEquiv.symm a) y :=
  vertexFiberMap _ _ (edgeCosliceSourceRestriction f)
    (edgeCosliceSourceRestriction_projection f) y

/-- 同じ指定点の fiber は、元の始点の coslice 内の左写像空間と厳密に同型。 -/
def edgeCosliceSourceMappingFiberIso (y : C _⦋0⦌)
    (g : (coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌) :
    vertexFiber (edgeCosliceSourceMapping f y) g ≅
      pinchedHomLeft (edgeCosliceVertex f.toTruncated) g.val :=
  vertexFiberMapFiberIso _ _ (edgeCosliceSourceRestriction f)
    (edgeCosliceSourceRestriction_projection f) y g ≪≫
      edgeCosliceSourceFiberIso f g.val

/-- 正規化した同じ始点制限は、全ホーンに関する fibration である。 -/
lemma edgeCosliceSourceMapping_fibration (y : C _⦋0⦌) :
    Fibration (edgeCosliceSourceMapping f y) := by
  have := coconeMappingSpace_restrict_fibration (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) y
  change Fibration (normalizedCoconeRestrictionFiber (SSet.yonedaEquiv.symm f.edge)
    (stdSimplex.δ (1 : Fin 2)) _ y)
  rw [normalizedCoconeRestrictionFiber_eq]
  infer_instance

/-- 全ての同じ写像空間が可縮なら、元の始点制限は自明 Kan fibration。 -/
lemma edgeCosliceSourceMapping_trivial_of_contractible
    (y : C _⦋0⦌)
    (h : ∀ g : (coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌,
      IsContractibleKan (pinchedHomLeft (edgeCosliceVertex f.toTruncated) g.val)) :
    TrivialKanFibration (edgeCosliceSourceMapping f y) := by
  let q := edgeCosliceSourceMapping f y
  have hq := (SSet.modelCategoryQuillen.fibration_iff q).mp
    (edgeCosliceSourceMapping_fibration f y)
  let : RightFibration q := ⟨by
    intro A B i hi
    cases hi with
    | @intro n k hk => exact hq _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ k)⟩
  apply rightFibration_trivialKanFibration_of_contractible_fibers q
  intro g
  exact isContractibleKan_of_iso (edgeCosliceSourceMappingFiberIso f y g).symm (h g)

/-- 同じ始点 coslice の全写像空間の可縮性から、元の辺への高次の局所性を得る。 -/
lemma isLocalForHom_of_coslice_mapping_contractible
    (y : C _⦋0⦌)
    (h : ∀ g : (coconeMappingSpace (SSet.yonedaEquiv.symm a) y) _⦋0⦌,
      IsContractibleKan (pinchedHomLeft (edgeCosliceVertex f.toTruncated) g.val)) :
    IsLocalForHom (Truncated.HomotopyCategory.homMk f.toTruncated) y := by
  have := edgeCosliceSourceMapping_trivial_of_contractible f y h
  have he := isQCatEquivalence_of_trivialKanFibration (edgeCosliceSourceMapping f y)
  have ha : stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge =
      SSet.yonedaEquiv.symm a := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact f.src_eq
  change IsQCatEquivalence (normalizedCoconeRestrictionFiber
    (SSet.yonedaEquiv.symm f.edge) (stdSimplex.δ (1 : Fin 2)) ha y) at he
  rw [normalizedCoconeRestrictionFiber_eq] at he
  have hraw := (qCatEquivalenceOfIso (eqToIso (congrArg
    (fun p ↦ coconeMappingSpace p y) ha))).isQCatEquivalence.cancel_right he
  have hc := (isLocalForHom_edge_iff_sourceRestriction
    (SSet.yonedaEquiv.symm f.edge) y).mpr hraw
  apply (isLocalForHom_homMk_iff_edgeOfSimplex f.toTruncated y).mpr
  have hc' := (isLocalForHom_homMk_iff_edgeOfSimplex
    (edgeCosliceEdge (SSet.yonedaEquiv.symm f.edge)) y).mp hc
  change IsLocalForHom (Truncated.HomotopyCategory.homMk
    (edgeOfSimplex (SSet.yonedaEquiv (SSet.yonedaEquiv.symm f.edge)))) y at hc'
  change IsLocalForHom (Truncated.HomotopyCategory.homMk (edgeOfSimplex f.edge)) y
  exact ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply f.edge) ▸ hc'

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
