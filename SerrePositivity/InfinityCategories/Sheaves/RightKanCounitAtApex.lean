module

public import SerrePositivity.InfinityCategories.Sheaves.RightKanMovingConeCounit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitShapeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomTransportSameEdge

/-!
概要：指定輸送の余単位を元の頂点に正規化し、同じ添字による制限と図式の等式での移送を計算する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma normalized_apex_eq {T : Type u} [Category T] {a b v : T}
    (m : a ⟶ b) (ha : a = v) (hb : b = v)
    (h : m ≫ eqToHom hb = eqToHom ha) :
    eqToHom ha.symm ≫ m = eqToHom hb.symm := by
  subst a b
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 錐の余単位を指定頂点に沿う等式で移す。 -/
def coneCounitAtApex {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) {v : X _⦋0⦌}
    (h : c.vertex = v) : FunctorHom (SSet.const v) p :=
  constantFunctorHomMap K (eqToHom (congrArg HomotopyCategory.mk h).symm) ≫ coneCounitHom c

/-- 指定輸送の余単位を元の頂点に正規化し、同じ添字による制限と図式の等式での移送を計算する。
Kerodon Definition 7.3.1.2（Tag 02Y9）。HTT 5.1.5.6 の指定右 Kan 輸送。 -/
lemma rightKan_transport_counit_atApex
    {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {v : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α v) :
    let c := rightKanCanonicalCone δ F v
    coneCounitAtApex t.cone t.cone_vertex =
      coneCounitAtApex c (rightKanCanonicalCone_vertex δ F v) ≫
        (hoFunctor.map ((pre (rightKanProjection δ v)).app D)).toFunctor.map
          (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)) := by
  intro c
  let L := rightKanShape δ v
  let vc := rightKanCanonicalCone_vertex δ F v
  let g : FunctorHom c.val t.cone.val := Truncated.HomotopyCategory.homMk t.edge
  let a : (HomotopyCategory.mk c.vertex : hoFunctor.obj D) ⟶
    HomotopyCategory.mk t.cone.vertex :=
      functorHomEvaluate g (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) L))
  have ha := normalized_apex_eq a (congrArg HomotopyCategory.mk vc)
    (congrArg HomotopyCategory.mk t.cone_vertex) (rightKan_transport_apex_eval t)
  have h := rightKan_transport_counit_comp t
  let i : (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) v) : hoFunctor.obj D) ⟶
      HomotopyCategory.mk c.vertex := eqToHom (congrArg HomotopyCategory.mk vc).symm
  let gα := (hoFunctor.map ((pre (rightKanProjection δ v)).app D)).toFunctor.map
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
  calc
    _ = constantFunctorHomMap L (i ≫ a) ≫ coneCounitHom t.cone :=
      congrArg (fun m => constantFunctorHomMap L m ≫ coneCounitHom t.cone) ha.symm
    _ = constantFunctorHomMap L i ≫ (constantFunctorHomMap L a ≫ coneCounitHom t.cone) := by
      rw [constantFunctorHomMap_comp, Category.assoc]
    _ = constantFunctorHomMap L i ≫ (coneCounitHom c ≫ gα) :=
      congrArg (fun m => constantFunctorHomMap L i ≫ m) h
    _ = _ := (Category.assoc _ _ _).symm

/-- 指定頂点に移した余単位は、同じ添字の制限で保たれる。 -/
lemma coneCounitAtApex_shapeRestriction {J K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (i : J ⟶ K) {v : X _⦋0⦌} (hv : c.vertex = v) :
    kanFunctorHomCongr (V := i ≫ p) (SSet.comp_const i v) rfl
      ((hoFunctor.map ((pre i).app X)).toFunctor.map (coneCounitAtApex c hv)) =
    coneCounitAtApex (restrictJoinCone c i) ((restrictJoinCone_vertex c i).trans hv) := by
  subst v
  unfold coneCounitAtApex
  simp only [eqToHom_refl, constantFunctorHomMap_id, Category.id_comp]
  rw [coneCounitHom_shapeRestriction]
  unfold kanFunctorHomCongr
  simp only [Iso.homCongr_apply, eqToIso.inv, eqToIso.hom, eqToHom_refl,
    Category.comp_id, Category.id_comp]

/-- 図式の等式で移した余単位の計算。 -/
lemma coneCounitAtApex_cast {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCone p) (h : p = q) {v : X _⦋0⦌} (hv : c.vertex = v) :
    coneCounitAtApex (c.cast h) ((JoinCone.vertex_cast _ h).trans hv) =
      kanFunctorHomCongr rfl h (coneCounitAtApex c hv) := by
  subst q
  simp [JoinCone.cast, kanFunctorHomCongr]

end SerrePositivity.InfinityCategories.Sheaves
