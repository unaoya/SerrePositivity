module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.RelativeNaturalComparison
public import SerrePositivity.EInfinity.Modules.LocalizationComparisonEvaluation
public import SerrePositivity.EInfinity.Modules.LocalizationStrictIdentity

/-!
# 同じ円筒比較の指定された交差辺

概要：HA §1.3.4 の円筒の同じ交差射を、局所化後の指定成分に照合する。
方針：全係数写像の指定辺の保存と同じ端点の等式を使う。
規約：元の二つの包含と元の交差射を保つ。
使われ方：M10 の全比較と元の弱自然変換の成分の一致。
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
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open scoped Simplicial

/-- 概要：指定生成辺の係数作用は同じ端点輸送と整合する（HTT §1.1.5）。
方針：実際の一単体の等式を同じホモトピー圏の類へ移す。
規約：元の射と係数関手。使われ方：円筒の交差辺の射影。 -/
lemma localizationStrictHom_coefficient_class {C D : RelativeCategory.{u}} (F : C ⟶ D)
    {X Y : C.category} (f : X ⟶ Y) :
    eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex F X)).symm ≫
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap F)).toFunctor.map
        (SSet.HomotopyCategory.homMk (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f))) ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex F Y)) =
        SSet.HomotopyCategory.homMk
          (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom D (F.functor.map f))) := by
  exact MorphismSpaces.homMk_transport
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex F X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex F Y)
    ((coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f)).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap F)).toTruncated
    (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom D (F.functor.map f))).toTruncated
    (localizationStrictEdge_coefficient F f)

variable (C : RelativeCategory.{u})

/-- 概要：同じ円筒の両端点の射影は元の全頂点で恒等（HA §1.3.4）。
方針：同じ相対関手の合成の厳密な等式を評価する。
規約：局所化後の全ての頂点。使われ方：交差辺の射影の両端点。 -/
lemma relativeCylinderEndpoint_projection_vertex (i : Fin 2) (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve C) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x) = x := by
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C i) ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C)).app (Opposite.op ⦋0⦌) x = x
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_comp, relativeCylinderEndpoint_projection, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_id]
  rfl

/-- 概要：元の円筒交差射の同じ類を、二つの全包含の像の端点で表す（HA §1.3.4）。
方針：指定生成辺に元の頂点比較の等式だけを前後合成する。
規約：新たな可逆辺を選ばない。使われ方：全比較の成分の同定。 -/
def relativeCylinderCrossingClass (X : C.category) :
    SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C 0)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C X)) ⟶
    SSet.HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderEndpoint C 1)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C X)) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex (relativeCylinderEndpoint C 0) X)) ≫
  SSet.HomotopyCategory.homMk (coherentNerveEdge
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom (relativeCylinder C) ((relativeCylinderContraction C).app (1, X)))) ≫
  eqToHom (congrArg SSet.HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex (relativeCylinderEndpoint C 1) X)).symm

/-- 概要：同じ交差辺は射影で指定恒等の類へ移る（HA §1.3.4）。
方針：同じ係数作用の指定辺の保存、恒等の類、端点の輸送を照合する。
規約：両端の全包含を保持する。使われ方：逆の比較の自然性で成分を回収する。 -/
lemma relativeCylinderCrossingClass_projection (X : C.category) :
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 0 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C X))).symm ≫
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C))).toFunctor.map
      (relativeCylinderCrossingClass C X) ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 1 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C X))) = 𝟙 _ := by
  have h := localizationStrictHom_coefficient_class (relativeCylinderProjection C)
    ((relativeCylinderContraction C).app (1, X))
  have hm := congrArg (fun k =>
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex (relativeCylinderProjection C) (0, X))) ≫ k ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex (relativeCylinderProjection C) (1, X))).symm) h
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] at hm
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (relativeCylinderProjection C))).toFunctor.map
      (SSet.HomotopyCategory.homMk (coherentNerveEdge
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom (relativeCylinder C)
          ((relativeCylinderContraction C).app (1, X))))) =
    eqToHom _ ≫ SSet.HomotopyCategory.homMk
      (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C (𝟙 X))) ≫ eqToHom _ at hm
  rw [localizationStrictHom_id] at hm
  simp only [relativeCylinderCrossingClass, CategoryTheory.Functor.map_comp, eqToHom_map]
  rw [hm]
  simp only [Category.assoc, Category.id_comp, Category.comp_id, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl]

attribute [cite HTT "1.1.5.5" (partial := component)
  "同じ係数関手の指定一単体と頂点比較を、ホモトピー圏の類で照合する部分。"]
  localizationStrictHom_coefficient_class
attribute [cite HTT "1.2.7" (partial := component)
  "同じ円筒による全比較の元の交差辺と射影の計算だけ。一般の局所化の普遍性は含まない。"]
  relativeCylinderEndpoint_projection_vertex relativeCylinderCrossingClass
  relativeCylinderCrossingClass_projection

end SerrePositivity.EInfinity.Modules
