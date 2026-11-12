module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceCommaEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalReplacementUniversal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionBaseEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrismPoint

/-!
概要：元の局所置換を区間型 comma の指定した始対象へ移す。
方針：始点の表示だけを正規化し、標準 coslice 比較で始対象性と元の辺を移す。
規約：局所置換の存在は仮定しない。与えられた辺の普遍性を証明する。
使われ方：局所置換から coherent な反射を選ぶための普遍矢印。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {X : SSet.{u}} [Quasicategory X]

/-- 元の図式の等式による局所余錐の移送は、余錐そのものの移送と可換。 -/
lemma localTargetCoconeSpace_transport_fst (W : Set (X _⦋1⦌)) {K : SSet.{u}}
    {D d : K ⟶ X} (h : D = d) :
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeSpace W) h) ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection d) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι ≫
        eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 元の局所置換の辺を表す、固定始点の comma 内の指定点。 -/
def localReplacementCommaPoint (W : Set (X _⦋1⦌)) (e : (Δ[1] : SSet.{u}) ⟶ X)
    (x : X _⦋0⦌) (hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι x :=
  SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeSourcePointCocone e)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeSourcePointCocone_vertex]; exact hy)) ≫
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeSpace W) hx) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCommaComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι x

/-- 元の局所同値は、局所包含の固定始点 comma の始対象を与える。 -/
lemma localReplacementCommaPoint_isInitial (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W)
    (x : X _⦋0⦌) (hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv (localReplacementCommaPoint W e x hx hy)) := by
  unfold localReplacementCommaPoint
  rw [SSet.yonedaEquiv_comp, NatTrans.comp_app_apply, Equiv.apply_symm_apply]
  let hnorm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeSpace W) hx))
  have hn := hnorm.map_isInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localReplacement_edgeSource_isInitial W e he hy)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeSpace] at hn ⊢
  let hcomp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCommaComparison_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι x).choose
  exact hcomp.map_isInitialVertex hn

/-- 指定 comma 点の元の矢印の族は、元の局所置換の辺そのもの。 -/
lemma localReplacementCommaPoint_uncurry (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (x : X _⦋0⦌)
    (hx : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry (localReplacementCommaPoint W e x hx hy ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι) x) =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ e := by
  unfold localReplacementCommaPoint
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCommaComparison_uncurry, Category.assoc,
    localTargetCoconeSpace_transport_fst W hx, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom hx, SSet.yonedaEquiv_symm_comp]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeSpace]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localTargetCoconeVertex_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism (Δ[0] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ e = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism_point, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_point, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- 各対象から局所対象への局所同値が存在すれば、局所包含の各 comma に始対象が存在。 -/
lemma unitCommaFiber_initial_exists_of_localReplacements (W : Set (X _⦋1⦌))
    (hreplace : ∀ x : X _⦋0⦌, ∃ (y : X _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W y) (x : X _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W).ι x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  obtain ⟨y, a, ha, hy⟩ := hreplace x
  let e := SSet.yonedaEquiv.symm a.edge
  have he : SSet.yonedaEquiv e ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
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
  have hy' := (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W) hyv).mpr hy
  exact ⟨_, localReplacementCommaPoint_isInitial W e he x hx hy'⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
