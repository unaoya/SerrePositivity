module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportApexHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportDiagramHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitMorphismNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeMorphismBoundary

/-!
概要：指定右 Kan 輸送の終端の余単位を、標準錐の同じ余単位と図式側の変換の合成で表す。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 錐の射の余単位自然性を、同じ係数への指定変換と合成する。 -/
lemma movingCone_counit_comp
    {K X : SSet.{u}} [Quasicategory X] {p q r : K ⟶ X}
    (c : JoinCone p) (d : JoinCone q) (m : FunctorHom c.val d.val)
    (α : FunctorHom p r) (β : FunctorHom q r)
    (h : kanFunctorHomCongr c.property d.property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map m) ≫ β = α) :
    constantFunctorHomMap K
      (functorHomEvaluate m (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))) ≫
        (coneCounitHom d ≫ β) = coneCounitHom c ≫ α := by
  let a : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex :=
    functorHomEvaluate m (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))
  let b : FunctorHom p q := kanFunctorHomCongr c.property d.property
    ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map m)
  have hn : constantFunctorHomMap K a ≫ coneCounitHom d = coneCounitHom c ≫ b :=
    coneCounitHom_morphism_naturality c d m
  change constantFunctorHomMap K a ≫ (coneCounitHom d ≫ β) = _
  calc
    _ = (constantFunctorHomMap K a ≫ coneCounitHom d) ≫ β := (Category.assoc _ _ _).symm
    _ = (coneCounitHom c ≫ b) ≫ β := congrArg (fun k => k ≫ β) hn
    _ = coneCounitHom c ≫ (b ≫ β) := Category.assoc _ _ _
    _ = coneCounitHom c ≫ α := congrArg (fun k => coneCounitHom c ≫ k) h

/-- 極限錐の余単位で頂点射の一致を検出する。 -/
lemma cone_apex_eq_of_counit_fac
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} {c d : JoinCone p}
    (hd : IsLimitCone d)
    (k : (SSet.HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶
      SSet.HomotopyCategory.mk d)
    (a : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex)
    (h : constantFunctorHomMap K a ≫ coneCounitHom d = coneCounitHom c) :
    a = (hoFunctor.map (sliceOverProjection p)).toFunctor.map k :=
  (coneCounitHom_bijective d hd c.vertex).injective
    (h.trans (coneCounitHom_coneMorphism k).symm)

/-- 指定右 Kan 輸送の終端の余単位を、標準錐の同じ余単位と図式側の変換の合成で表す。
Kerodon Definition 7.3.1.2（Tag 02Y9）。HTT 5.1.5.6 の指定右 Kan 輸送の計算。 -/
lemma rightKan_transport_counit_comp
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {v : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α v) :
    let L := rightKanShape δ v
    let c := rightKanCanonicalCone δ F v
    let g : FunctorHom c.val t.cone.val := Truncated.HomotopyCategory.homMk t.edge
    constantFunctorHomMap L (functorHomEvaluate g
        (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) L))) ≫ coneCounitHom t.cone =
      coneCounitHom c ≫
        (hoFunctor.map ((pre (rightKanProjection δ v)).app D)).toFunctor.map
          (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)) := by
  intro L c g
  exact (coneCounitHom_morphism_naturality c t.cone g).trans
    (congrArg (fun m => coneCounitHom c ≫ m) t.diagram_hom)

private lemma apex_normalize {T : Type u} [Category T] {a b c d v : T}
    (f : a ⟶ b) (hc : a = c) (hd : b = d) (hv : d = v) (hcv : c = v)
    (h : f ≫ eqToHom (hd.trans hv) = eqToHom (hc.trans hcv)) :
    (eqToHom hc.symm ≫ f ≫ eqToHom hd) ≫ eqToHom hv = eqToHom hcv := by
  subst c d v
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 指定右 Kan 輸送は、元の頂点の等式を保つ。 -/
lemma rightKan_transport_apex_eval
    {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {v : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α v) :
    let L := rightKanShape δ v
    let c := rightKanCanonicalCone δ F v
    let g : FunctorHom c.val t.cone.val := Truncated.HomotopyCategory.homMk t.edge
    let vc : c.vertex = F.app (Opposite.op ⦋0⦌) v := rightKanCanonicalCone_vertex δ F v
    functorHomEvaluate g (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) L)) ≫
        eqToHom (congrArg HomotopyCategory.mk t.cone_vertex) =
      eqToHom (congrArg HomotopyCategory.mk vc) := by
  intro L c g vc
  let a := coneApexEvaluation L D
  have h := t.apex_hom
  let hc := coneApexEvaluation_vertex c
  let hd := coneApexEvaluation_vertex t.cone
  let e := (hoFunctor.map a).toFunctor.map g
  have he : e ≫ eqToHom (congrArg HomotopyCategory.mk (hd.trans t.cone_vertex)) =
      eqToHom (congrArg HomotopyCategory.mk (hc.trans vc)) := h
  change (eqToHom (congrArg HomotopyCategory.mk hc).symm ≫ e ≫
      eqToHom (congrArg HomotopyCategory.mk hd)) ≫
        eqToHom (congrArg HomotopyCategory.mk t.cone_vertex) = _
  exact apex_normalize e (congrArg HomotopyCategory.mk hc) (congrArg HomotopyCategory.mk hd)
    (congrArg HomotopyCategory.mk t.cone_vertex) (congrArg HomotopyCategory.mk vc) he

end SerrePositivity.InfinityCategories.Sheaves
