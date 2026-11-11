module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：任意のホモトピーが誘導する前合成作用の自然変換。
方針：内部 Hom の豊穣な前合成作用に代表辺を写し、ホモトピー圏で評価する。
規約：ホモトピーの可逆性も始域の quasicategory 性も要求しない。
使われ方：写像円柱の右端への制限の Hom 対応と単位の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：ホモトピーを前合成作用の間の辺へ移す。
方針：豊穣な前合成作用の射で元の辺を写す。
規約：任意の単体集合を扱う。
使われ方：非可逆な単位が誘導する前合成作用。 -/
def precompositionHomotopyEdge {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (Z : SSet.{u}) :
    SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom B).obj Z)).obj ((ihom A).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre f).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre g).app Z)) where
  edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z).app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge
  src_eq := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z))).src_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex f)
  tgt_eq := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z))).tgt_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex g)

/-- 概要：ホモトピーから前合成のホモトピー圏の自然変換を得る。
方針：前合成作用の辺の類を通常の自然変換へ評価する。
規約：可逆性を入力しない。
使われ方：右端への制限の逆写像の自然性。 -/
def precompositionNatTrans {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (Z : SSet.{u}) :
    (hoFunctor.map ((pre f).app Z)).toFunctor ⟶
      (hoFunctor.map ((pre g).app Z)).toFunctor :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans
    (SSet.Truncated.HomotopyCategory.homMk (precompositionHomotopyEdge H Z))

/-- 概要：前合成作用の辺を関手で評価すると元のホモトピーの後合成となる。
方針：豊穣前合成の評価の公式と curry の後合成自然性を用いる。
規約：等式は一次単体の厳密な等式。
使われ方：単位の成分と元の指定ホモトピーの照合。 -/
lemma precompositionHomotopyEdge_evaluate {A B Z : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (U : B ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)).app (Opposite.op ⦋1⦌)
      (precompositionHomotopyEdge H Z).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H U)).edge := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorPrecompositionMap_evaluate (A := A) U) (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)).app (Opposite.op ⦋1⦌)
      (precompositionHomotopyEdge H Z).edge =
    ((ihom A).map U).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge at h
  rw [h]
  change ((ihom A).map U).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
    SSet.yonedaEquiv (curry (H.h ≫ U))
  rw [← SSet.yonedaEquiv_comp, curry_natural_right]

/-- 概要：前合成の自然変換の関手 U での成分は、元のホモトピーの U による像。
方針：評価関手の代表辺を比較し、豊穣前合成の評価の等式を使う。
規約：始域と標的の quasicategory 性は不要。
使われ方：写像円柱の単位の自然性と両三角恒等式。 -/
lemma precompositionNatTrans_app {A B Z : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (U : B ⟶ Z) :
    (precompositionNatTrans H Z).app (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H U)) := by
  unfold precompositionNatTrans _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  change SSet.Truncated.HomotopyCategory.homMk _ =
    SSet.Truncated.HomotopyCategory.homMk _
  congr 1

/-- 概要：時間に定値なホモトピーの類は端点の等式による恒等射。
方針：終点を始点へ置き換え、定値ホモトピーの類の公式に帰着する。
規約：端点は定義上等しい必要はない。
使われ方：円柱の変形を固定部分へ制限した三角恒等式。 -/
lemma homotopyHom_eqToHom {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (hfg : f = g)
    (hH : H.h = CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ f) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hfg) := by
  subst g
  have h : H = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f := by
    apply SSet.RelativeMorphism.Homotopy.ext
    exact hH
  rw [h, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
