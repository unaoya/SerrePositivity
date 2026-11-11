module

public import SerrePositivity.KST.Spectra.PointedVerticalChains
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary

/-!
概要：元の射影を固定する点つき区間と有限鎖を、同じ内部 Hom の実際の fiber へ持ち上げる。
方針：指定した射の頂点上の pullback に端点と区間全体を持ち上げ、包含で計算する。
規約：この段階では Kan 性不要。使われ方：垂直有限鎖から単一の垂直区間の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 指定した点つき射と同じ射影を持つ、元の内部 Hom の実際の fiber。 -/
abbrev verticalFiber {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (r : T ⟶ E) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p))

/-- 元の点つき射の零次パラメータ族の後合成は、元の合成の同じパラメータ族。 -/
lemma pointFamily_post {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (s : T ⟶ E) :
    pointFamily s ≫ (PointedObject.basedHomMap T p).right = pointFamily (s ≫ p) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  exact familyVertex_post s p

/-- 元の零次パラメータ族は、その元の頂点に値を取る定数射。 -/
lemma pointFamily_eq_const {T E : PointedSimplicialSet.{u}} (s : T ⟶ E) :
    pointFamily s = SSet.const (familyVertex s) := by
  rw [← SSet.yonedaEquiv_symm_zero]
  exact (SSet.yonedaEquiv.symm_apply_apply (pointFamily s)).symm

/-- 同じ射影を持つ元の段射を、指定した Hom fiber の頂点として読む。 -/
def verticalFiberVertex {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (r s : T ⟶ E)
    (hs : s ≫ p = r ≫ p) : (verticalFiber p r) _⦋0⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p))
    (pointFamily s) (by rw [pointFamily_post, hs, pointFamily_eq_const]))

/-- fiber の頂点を元の Hom へ含めると、元の段射の同じ頂点になる。 -/
lemma verticalFiberVertex_ι {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (r s : T ⟶ E)
    (hs : s ≫ p = r ≫ p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p))).app _
      (verticalFiberVertex p r s hs) = familyVertex s := by
  rw [verticalFiberVertex, ← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
  rfl

namespace VerticalPath
variable {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}

/-- 垂直な元の区間全体を、指定した Hom fiber の辺として持ち上げる。 -/
def fiberEdge (H : VerticalPath p f g) (r : T ⟶ E) (hf : f ≫ p = r ≫ p) :
    (verticalFiber p r).Edge (verticalFiberVertex p r f hf)
      (verticalFiberVertex p r g (H.endpoint_over.trans hf)) := by
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p)) H.path
    (H.over.trans (congrArg (fun s ↦ SSet.const (familyVertex s)) hf))
  have h0 : stdSimplex.δ (1 : Fin 2) ≫ l =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p)) (pointFamily f)
        (by rw [pointFamily_post, hf, pointFamily_eq_const]) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, H.zero, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
  have h1 : stdSimplex.δ (0 : Fin 2) ≫ l =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p)) (pointFamily g)
        (by rw [pointFamily_post, H.endpoint_over, hf, pointFamily_eq_const]) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, H.one, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
  exact SSet.Edge.mk (SSet.yonedaEquiv l)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, h0]; rfl)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, h1]; rfl)

/-- fiber 内の辺を含めると、元の射影を全区間で固定する点つき区間になる。 -/
def ofFiberEdge (p : E ⟶ B) (r f g : T ⟶ E)
    (hf : f ≫ p = r ≫ p) (hg : g ≫ p = r ≫ p)
    (e : (verticalFiber p r).Edge (verticalFiberVertex p r f hf) (verticalFiberVertex p r g hg)) :
    VerticalPath p f g where
  path := SSet.yonedaEquiv.symm e.edge ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (PointedObject.basedHomMap T p).right (familyVertex (r ≫ p))
  zero := by
    rw [← Category.assoc, SSet.Edge.δ_one_yonedaEquiv_symm]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact verticalFiberVertex_ι p r f hf
  one := by
    rw [← Category.assoc, SSet.Edge.δ_zero_yonedaEquiv_symm]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact verticalFiberVertex_ι p r g hg
  «over» := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, SSet.comp_const, hf]

end VerticalPath

namespace VerticalChain

/-- 元の垂直有限鎖の両端は、同じ Hom fiber の同じ成分に属する。 -/
lemma fiber_component {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}
    (H : VerticalChain p f g) (r : T ⟶ E) (hf : f ≫ p = r ≫ p) :
    π₀.mk (verticalFiberVertex p r f hf) =
      π₀.mk (verticalFiberVertex p r g (H.endpoint_over.trans hf)) := by
  induction H with
  | refl => rfl
  | @tail b c h H ih =>
    obtain ⟨H⟩ := H
    exact ih.trans (π₀.sound (H.fiberEdge r ((VerticalChain.endpoint_over h).trans hf)))

end VerticalChain
end SerrePositivity.KST.Spectra.PointedMapping
