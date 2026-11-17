module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.RelativeCylinderPrescribedEdge

/-!
# 円筒の全比較の同じ指定成分

概要：HTT §1.2.7 の全関手間の比較を元の円筒交差辺に照合する。
方針：選択逆の同じ可逆二胞体の自然性を、射影の恒等の法則に適用する。
規約：同じ選択逆・同じ比較・同じ交差射を保持する。
使われ方：M10 の弱自然変換の全比較の指定成分を回収する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open scoped Simplicial
variable (C : RelativeCategory.{u})

/-- 概要：同じ選択逆から各端点への比較の成分を計算する（HTT §1.2.7）。
方針：全関手の等式と前合成の評価を同じ選択逆の可逆二胞体に適用する。
規約：元の比較の成分。使われ方：全端点比較の指定射との一致。 -/
lemma relativeCylinderInverseEndpointIso_component (i : Fin 2)
    (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve C) _⦋0⦌) :
    ((relativeCylinderInverseEndpointIso C i).app x).hom =
      eqToHom (congrArg (fun v => SSet.HomotopyCategory.mk
        ((relativeCylinderProjection_isQCatEquivalence C).choose.inv.app (Opposite.op ⦋0⦌) v))
        (relativeCylinderEndpoint_projection_vertex C i x)).symm ≫
      (((relativeCylinderProjection_isQCatEquivalence C).choose.homInvIso).app
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x)).hom := by
  unfold relativeCylinderInverseEndpointIso
  simp only [FunctorIso.app_trans, Iso.trans_hom]
  simp only [FunctorIso.app, Iso.app_hom, functorIso_eqToIso_hom_app,
    functorIso_precomp_hom_app,
    eqToHom_refl, Category.comp_id]
  simp only [FunctorIso.toNatIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, eqToIso.inv, NatTrans.comp_app, eqToHom_app,
    CategoryTheory.Functor.mapIso_hom, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：射影で恒等となる同じ射は全端点比較の成分である（HTT §1.2.7）。
方針：選択逆の同じ可逆二胞体の自然性に射影の恒等の法則を適用する。
規約：同じ全比較そのもの。使われ方：指定された円筒交差辺の回収。 -/
lemma relativeCylinderEndpointIso_component_of_projection
    (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve C) _⦋0⦌)
    (a : SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C 0)).app (Opposite.op ⦋0⦌) x) ⟶
      SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C 1)).app (Opposite.op ⦋0⦌) x))
    (ha : eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 0 x)).symm ≫
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C))).toFunctor.map a ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk
        (relativeCylinderEndpoint_projection_vertex C 1 x)) = 𝟙 _) :
    ((relativeCylinderEndpointIso C).app x).hom = a := by
  let e := (relativeCylinderProjection_isQCatEquivalence C).choose
  let P := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C)
  let y (i : Fin 2) :=
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x
  let d (i : Fin 2) : SSet.HomotopyCategory.mk (P.app (Opposite.op ⦋0⦌) (y i)) ≅
      SSet.HomotopyCategory.mk x :=
    eqToIso (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C i x))
  let ε (i : Fin 2) := e.homInvIso.app (y i)
  have hi (i : Fin 2) : (relativeCylinderInverseEndpointIso C i).app x =
      ((hoFunctor.map e.inv).toFunctor.mapIso (d i)).symm ≪≫ ε i := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv, d, ε,
      eqToIso.inv, eqToHom_map] using relativeCylinderInverseEndpointIso_component C i x
  have hp := congrArg (fun k => (d 0).hom ≫ k ≫ (d 1).inv) ha
  change (d 0).hom ≫ ((d 0).inv ≫ (hoFunctor.map P).toFunctor.map a ≫ (d 1).hom) ≫
    (d 1).inv = (d 0).hom ≫ 𝟙 _ ≫ (d 1).inv at hp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id, Category.id_comp] at hp
  have hn := e.homInvIso.toNatIso.hom.naturality a
  change (hoFunctor.map (e.hom ≫ e.inv)).toFunctor.map a ≫
      (ε 1).hom = (ε 0).hom ≫ (hoFunctor.map (𝟙 _)).toFunctor.map a at hn
  have hmap := CategoryTheory.Functor.congr_hom
    (congrArg Cat.Hom.toFunctor (hoFunctor.map_comp e.hom e.inv)) a
  simp only [Cat.Hom.comp_toFunctor, CategoryTheory.Functor.comp_map,
    eqToHom_refl, Category.id_comp, Category.comp_id] at hmap
  have hid := CategoryTheory.Functor.congr_hom
    (congrArg Cat.Hom.toFunctor (hoFunctor.map_id (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (relativeCylinder C)))) a
  simp only [Cat.Hom.id_toFunctor, CategoryTheory.Functor.id_map,
    eqToHom_refl, Category.id_comp, Category.comp_id] at hid
  rw [hmap, hid] at hn
  change (hoFunctor.map e.inv).toFunctor.map ((hoFunctor.map P).toFunctor.map a) ≫
      (ε 1).hom = (ε 0).hom ≫ a at hn
  rw [hp, CategoryTheory.Functor.map_comp] at hn
  rw [relativeCylinderEndpointIso, FunctorIso.app_trans, FunctorIso.app_symm, hi 0, hi 1]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv]
  have h := congrArg (fun k => (ε 0).inv ≫ k) hn
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

/-- 概要：全端点比較の成分は元の指定交差辺の同じ類（HTT §1.2.7）。
方針：同じ交差辺の射影の恒等の法則を全比較の成分の判定に渡す。
規約：元の辺を別の可逆辺に取り替えない。使われ方：弱自然変換の指定成分。 -/
lemma relativeCylinderEndpointIso_component (X : C.category) :
    ((relativeCylinderEndpointIso C).app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C X)).hom =
      relativeCylinderCrossingClass C X :=
  relativeCylinderEndpointIso_component_of_projection C _ _
    (relativeCylinderCrossingClass_projection C X)

attribute [cite HTT "1.2.7" (partial := component)
  "同じ円筒の全関手間の比較の指定成分を、元の交差射の類へ照合する法則のみ。"]
  relativeCylinderInverseEndpointIso_component
  relativeCylinderEndpointIso_component_of_projection relativeCylinderEndpointIso_component

end SerrePositivity.EInfinity.Modules
