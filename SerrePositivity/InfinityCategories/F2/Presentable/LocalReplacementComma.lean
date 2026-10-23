module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceCommaEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalReplacementUniversal
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation
public import SerrePositivity.InfinityCategories.F1.MappingSpacePrismPoint

/-!
概要：元の局所置換を区間型 comma の指定した始対象へ移す。
方針：始点の表示だけを正規化し、標準 coslice 比較で始対象性と元の辺を移す。
規約：局所置換の存在は仮定しない。与えられた辺の普遍性を証明する。
使われ方：局所置換から coherent な反射を選ぶための普遍矢印。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X : SSet.{u}} [Quasicategory X]

/-- 元の図式の等式による局所余錐の移送は、余錐そのものの移送と可換。 -/
lemma localTargetCoconeSpace_transport_fst (W : Set (X _⦋1⦌)) {K : SSet.{u}}
    {D d : K ⟶ X} (h : D = d) :
    eqToHom (congrArg (localTargetCoconeSpace W) h) ≫
        pullback.fst (sliceUnderProjection d) (localObjectsSubcomplex W).ι =
      pullback.fst (sliceUnderProjection D) (localObjectsSubcomplex W).ι ≫
        eqToHom (congrArg sliceUnder h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 元の局所置換の辺を表す、固定始点の comma 内の指定点。 -/
def localReplacementCommaPoint (W : Set (X _⦋1⦌)) (e : (Δ[1] : SSet.{u}) ⟶ X)
    (x : X _⦋0⦌) (hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x)
    (hy : IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    (Δ[0] : SSet.{u}) ⟶ unitCommaFiber (localObjectsSubcomplex W).ι x :=
  SSet.yonedaEquiv.symm (localTargetCoconeVertex W (edgeSourcePointCocone e)
    (by rw [edgeSourcePointCocone_vertex]; exact hy)) ≫
      eqToHom (congrArg (localTargetCoconeSpace W) hx) ≫
        cosliceCommaComparison (localObjectsSubcomplex W).ι x

/-- 元の局所同値は、局所包含の固定始点 comma の始対象を与える。 -/
lemma localReplacementCommaPoint_isInitial (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ localEquivalences W)
    (x : X _⦋0⦌) (hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x)
    (hy : IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    IsInitialVertex (SSet.yonedaEquiv (localReplacementCommaPoint W e x hx hy)) := by
  unfold localReplacementCommaPoint
  rw [SSet.yonedaEquiv_comp, NatTrans.comp_app_apply, Equiv.apply_symm_apply]
  let hnorm := qCatEquivalenceOfIso (eqToIso (congrArg (localTargetCoconeSpace W) hx))
  have hn := hnorm.map_isInitialVertex (localReplacement_edgeSource_isInitial W e he hy)
  dsimp only [localTargetCoconeSpace] at hn ⊢
  let hcomp := (cosliceCommaComparison_isQCatEquivalence (localObjectsSubcomplex W).ι x).choose
  exact hcomp.map_isInitialVertex hn

/-- 指定 comma 点の元の矢印の族は、元の局所置換の辺そのもの。 -/
lemma localReplacementCommaPoint_uncurry (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (x : X _⦋0⦌)
    (hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x)
    (hy : IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    unitCommaUncurry (localReplacementCommaPoint W e x hx hy ≫
      vertexFiberι (unitCommaSource (localObjectsSubcomplex W).ι) x) =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ e := by
  unfold localReplacementCommaPoint
  rw [← Category.assoc, cosliceCommaComparison_uncurry, Category.assoc,
    localTargetCoconeSpace_transport_fst W hx, ← Category.assoc,
    sliceUnderUncurry_eqToHom hx, SSet.yonedaEquiv_symm_comp]
  dsimp only [localTargetCoconeSpace]
  rw [localTargetCoconeVertex_fst, sliceUnderUncurry_yoneda]
  change leftMappingSpacePrism (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso 0 0).hom ≫ e = _
  rw [leftMappingSpacePrism_point, rightMappingSpacePrism_point, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- 各対象から局所対象への局所同値が存在すれば、局所包含の各 comma に始対象が存在。 -/
lemma unitCommaFiber_initial_exists_of_localReplacements (W : Set (X _⦋1⦌))
    (hreplace : ∀ x : X _⦋0⦌, ∃ (y : X _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      e.edge ∈ localEquivalences W ∧ IsLocalObject W y) (x : X _⦋0⦌) :
    ∃ v : (unitCommaFiber (localObjectsSubcomplex W).ι x) _⦋0⦌, IsInitialVertex v := by
  obtain ⟨y, a, ha, hy⟩ := hreplace x
  let e := SSet.yonedaEquiv.symm a.edge
  have he : SSet.yonedaEquiv e ∈ localEquivalences W := by
    simpa only [e, Equiv.apply_symm_apply] using ha
  have hea : SSet.yonedaEquiv e = a.edge := Equiv.apply_symm_apply SSet.yonedaEquiv a.edge
  have hxv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e) = x :=
    (stdSimplex.yonedaEquiv_δ_comp e (1 : Fin 2)).trans
      ((congrArg (fun s : X _⦋1⦌ ↦ X.δ 1 s) hea).trans a.src_eq)
  have hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x :=
    (Equiv.symm_apply_apply SSet.yonedaEquiv _).symm.trans (congrArg SSet.yonedaEquiv.symm hxv)
  have hyv : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e) = y :=
    (stdSimplex.yonedaEquiv_δ_comp e (0 : Fin 2)).trans
      ((congrArg (fun s : X _⦋1⦌ ↦ X.δ 0 s) hea).trans a.tgt_eq)
  have hy' := (congrArg (IsLocalObject W) hyv).mpr hy
  exact ⟨_, localReplacementCommaPoint_isInitial W e he x hx hy'⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
