module

public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.PointedBasedIntervalTraces
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOne

/-!
概要：π 同型に沿って実区間を移し、元の区間全体を写像 path 内に保持する。
方針：内部 Hom の写像 path 終点射の全単射 RLP で、両端を固定して持ち上げる。
規約：元の π 同型自身の RLP は仮定しない。使われ方：Ω 対象への交換区間の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 両端と基底の辺全体を固定する、全単射 RLP による区間の持ち上げ。 -/
lemma exists_interval_lift {E B : SSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p)
    (f g : (Δ[0] : SSet.{u}) ⟶ E) (P : (Δ[1] : SSet.{u}) ⟶ B)
    (h₀ : f ≫ p = stdSimplex.δ (1 : Fin 2) ≫ P)
    (h₁ : g ≫ p = stdSimplex.δ (0 : Fin 2) ≫ P) :
    ∃ L : (Δ[1] : SSet.{u}) ⟶ E,
      stdSimplex.δ (1 : Fin 2) ≫ L = f ∧
        stdSimplex.δ (0 : Fin 2) ≫ L = g ∧ L ≫ p = P := by
  let bd := HomotopyFunctionComplex.BoundaryOne.isColimit
  let a := bd.desc (BinaryCofan.mk f g)
  have ha₀ : boundary.ι (1 : Fin 2) ≫ a = f :=
    bd.fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩
  have ha₁ : boundary.ι (0 : Fin 2) ≫ a = g :=
    bd.fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩
  let boundaryLift : HasLiftingProperty (boundary 1).ι p := hp _ inferInstance
  let sq : CommSq a (boundary 1).ι p P := by
    constructor
    apply bd.hom_ext
    rintro ⟨j⟩
    cases j
    · change boundary.ι (1 : Fin 2) ≫ (a ≫ p) =
        boundary.ι (1 : Fin 2) ≫ ((boundary 1).ι ≫ P)
      rw [← Category.assoc, ha₀, ← Category.assoc, boundary.ι_ι, h₀]
    · change boundary.ι (0 : Fin 2) ≫ (a ≫ p) =
        boundary.ι (0 : Fin 2) ≫ ((boundary 1).ι ≫ P)
      rw [← Category.assoc, ha₁, ← Category.assoc, boundary.ι_ι, h₁]
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← boundary.ι_ι (1 : Fin 2), Category.assoc, sq.fac_left, ha₀]
  · rw [← boundary.ι_ι (0 : Fin 2), Category.assoc, sq.fac_left, ha₁]

/-- 移送された区間と、元の区間への全パラメータの写像 path トレース。 -/
structure TracedPathLift {T E B : PointedSimplicialSet.{u}} (q : E ⟶ B)
    {f g : T ⟶ E} (P : VerticalPath (PointedObject.toPoint B) (f ≫ q) (g ≫ q)) where
  path : VerticalPath (PointedObject.toPoint E) f g
  trace : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath (PointedObject.basedHomMap T q)).right
  zero : stdSimplex.δ (1 : Fin 2) ≫ trace =
    pointFamily f ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit (PointedObject.basedHomMap T q)).right
  one : stdSimplex.δ (0 : Fin 2) ≫ trace =
    pointFamily g ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit (PointedObject.basedHomMap T q)).right
  projection : trace ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (PointedObject.basedHomMap T q)).right = P.path
  retraction : trace ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction (PointedObject.basedHomMap T q)).right = path.path

/-- π 同型の写像 path 分解に元の同じ区間全体を持ち上げる。 -/
def TracedPathLift.choose {T E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (q : E ⟶ B)
    (hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right) {f g : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint B) (f ≫ q) (g ≫ q)) : TracedPathLift q P := by
  let m := PointedObject.basedHomMap T q
  let homE : KanComplex (PointedObject.basedHom T E).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let homB : KanComplex (PointedObject.basedHom T B).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  have hm : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism m.right := post_piIsomorphism T q hq
  have hu (a : T ⟶ E) :
      (pointFamily a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit m).right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection m).right =
        pointFamily (a ≫ q) := by
    rw [Category.assoc, ← Under.comp_right, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact familyVertex_post a q
  let hex := exists_interval_lift (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection m).right
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism m hm)
    (pointFamily f ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit m).right)
    (pointFamily g ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit m).right) P.path
    ((hu f).trans P.zero.symm) ((hu g).trans P.one.symm)
  let L := hex.choose
  have hL := hex.choose_spec
  let R := L ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction m).right
  have hr (a : T ⟶ E) :
      (pointFamily a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit m).right) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction m).right =
        pointFamily a := by
    rw [Category.assoc, ← Under.comp_right, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction,
      Under.id_right, Category.comp_id]
  have h₀ : stdSimplex.δ (1 : Fin 2) ≫ R = pointFamily f := by
    rw [← Category.assoc, hL.1, hr]
  have h₁ : stdSimplex.δ (0 : Fin 2) ≫ R = pointFamily g := by
    rw [← Category.assoc, hL.2.1, hr]
  let e : (PointedObject.basedHom T E).right.Edge (familyVertex f) (familyVertex g) :=
    SSet.Edge.mk (SSet.yonedaEquiv R)
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, h₀]; rfl)
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, h₁]; rfl)
  exact ⟨basedPathOfEdge e, L, hL.1, hL.2.1, hL.2.2,
    (Equiv.symm_apply_apply SSet.yonedaEquiv R).symm⟩

end SerrePositivity.KST.Spectra.PointedMapping
