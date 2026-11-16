module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.RelativeCylinderComponent

/-!
# 同じ弱自然変換の全局所化比較の指定成分

概要：HTT §1.2.7 の全関手比較の成分を、元の自然変換の指定辺の類に同定する。
方針：同じ円筒の成分の法則を後合成し、元の交差射の係数作用を計算する。
規約：元の全比較と同じ単位・余単位の射を保つ。
使われ方：M10 の BE 模型の往復比較と指定弱辺の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open scoped Simplicial
variable {C D : RelativeCategory.{u}} {F G : C ⟶ D}

/-- 概要：同じ円筒の交差射は元の自然変換の成分へ移る（HTT §1.2.7）。
方針：元の uncurrying の射作用と恒等射の保存を計算する。
規約：同じ自然変換の成分。使われ方：局所化した成分の生成辺の照合。 -/
lemma relativeNaturalCylinder_crossing (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    (relativeNaturalCylinder η hη).functor.map ((relativeCylinderContraction C).app (1, X)) =
      η.app X := by
  change η.app X ≫ G.functor.map (𝟙 X) = η.app X
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- 概要：同じ全比較の成分は円筒の成分の同じ後合成（HTT §1.2.7）。
方針：二つの全端点の等式の評価を個別に適用する。
規約：Arrow は同じ射の端点の等式も保持する。使われ方：元の成分との照合の分割。 -/
lemma localizationWeakNat_component_factorization (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (x : (localizationNerve C) _⦋0⦌) :
    Arrow.mk (((localizationNerveMapIsoOfWeakNatTrans η hη).app x).hom) =
      Arrow.mk ((hoFunctor.map (localizationNerveMap (relativeNaturalCylinder η hη))).toFunctor.map
        (((relativeCylinderEndpointIso C).app x).hom)) := by
  unfold localizationNerveMapIsoOfWeakNatTrans
  rw [functorIsoTransport_component_arrow]
  simp only [FunctorIso.app, Iso.app_hom, functorIso_toNatIso_postcomp_hom_app]

/-- 概要：同じ全比較の成分は元の弱自然変換の同じ生成射（HTT §1.2.7）。
方針：円筒の成分と同じ係数生成射の法則を Arrow の等式として貼る。
規約：同じ射・同じ端点の等式を保持する。使われ方：指定端点での式の kernel 照合。 -/
lemma localizationWeakNat_component_arrow (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    Arrow.mk (((localizationNerveMapIsoOfWeakNatTrans η hη).app
      (localizationNerveVertexEquiv C X)).hom) =
      Arrow.mk (SSet.HomotopyCategory.homMk
        (coherentNerveEdge (kanLocalizationStrictHom D (η.app X)))) := by
  let H := relativeNaturalCylinder η hη
  have hc := localizationStrictHom_coefficient_class H
    ((relativeCylinderContraction C).app (1, X))
  rw [relativeNaturalCylinder_crossing] at hc
  have hm := congrArg (fun k =>
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex H (0, X))) ≫ k ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex H (1, X))).symm) hc
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] at hm
  have he : (relativeCylinderEndpointIso C).toNatIso.hom.app
      (SSet.HomotopyCategory.mk (localizationNerveVertexEquiv C X)) =
      relativeCylinderCrossingClass C X := relativeCylinderEndpointIso_component C X
  have drop {a b c d : (localizationNerve D).HomotopyCategory}
      (ha : a = b) (k : b ⟶ c) (hd : c = d) :
      Arrow.mk (eqToHom ha ≫ k ≫ eqToHom hd) = Arrow.mk k := by
    subst b d
    simp
  rw [localizationWeakNat_component_factorization]
  change Arrow.mk ((hoFunctor.map (localizationNerveMap H)).toFunctor.map
    ((relativeCylinderEndpointIso C).toNatIso.hom.app
      (SSet.HomotopyCategory.mk (localizationNerveVertexEquiv C X)))) = _
  rw [he]
  simp only [relativeCylinderCrossingClass, CategoryTheory.Functor.map_comp, eqToHom_map]
  rw [hm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  exact drop _ _ _

/-- 概要：全局所化比較の成分は元の弱自然変換の同じ指定辺の類（HTT §1.2.7）。
方針：同じ Arrow の等式を、指定された頂点比較の等式で両端だけ移す。
規約：全比較そのものと同じ端点輸送。使われ方：指定弱単位・余単位の回収。 -/
lemma localizationNerveMapIsoOfWeakNatTrans_component (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F X)).symm ≫
      ((localizationNerveMapIsoOfWeakNatTrans η hη).app (localizationNerveVertexEquiv C X)).hom ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex G X)) =
      SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom D (η.app X))) := by
  obtain ⟨hx, hy, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (localizationWeakNat_component_arrow η hη X)
  have hh := congrArg (fun k =>
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F X)).symm ≫ k ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex G X))) h
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] using hh

attribute [cite HTT "1.2.7" (partial := component)
  "元の弱自然変換から作った同じ全局所化比較の指定成分を照合する法則。一般の普遍性は含まない。"]
  relativeNaturalCylinder_crossing localizationWeakNat_component_factorization
  localizationWeakNat_component_arrow localizationNerveMapIsoOfWeakNatTrans_component

end SerrePositivity.EInfinity.Modules
