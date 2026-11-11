module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.DegenerateFunctorHomSquare

/-!
概要：指定三辺の合成三角形を端点正規化とともに制限する。
方針：raw な三辺の前合成条件から同じ二単体の前合成を使う。
規約：端点の定義的等しさを要求せず、代表辺の raw な一致を要求する。
使われ方：B1 の恒等矢印の族に沿った単位の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：合成三角形を raw な三辺の条件で制限する。
方針：図式を前合成の内部 Hom に写し、uncurry の自然性を使う。
規約：制限後の三辺の端点は正規化したものを許す。
使われ方：引き戻しの射影の等式を使った恒等矢印での回収。 -/
def FunctorCompositionTriangle.precompOfRaw {A B X : SSet.{u}}
    {U V W : A ⟶ X} {U' V' W' : B ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W} {d : SSet.Homotopy U W}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) (i : B ⟶ A)
    (l' : SSet.Homotopy U' V') (r' : SSet.Homotopy V' W') (d' : SSet.Homotopy U' W')
    (hl : l'.h = (i ▷ (Δ[1] : SSet.{u})) ≫ l.h)
    (hr : r'.h = (i ▷ (Δ[1] : SSet.{u})) ≫ r.h)
    (hd : d'.h = (i ▷ (Δ[1] : SSet.{u})) ≫ d.h) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l' r' d' where
  diagram := T.diagram ≫ (pre i).app X
  face_zero := by
    rw [← Category.assoc, T.face_zero]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hr.symm
  face_one := by
    rw [← Category.assoc, T.face_one]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hd.symm
  face_two := by
    rw [← Category.assoc, T.face_two]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hl.symm

/-- 概要：指定三辺の合成三角形から h Fun の合成関係を得る。
方針：同じ三角形を恒等下辺の正方形へ補完して合成公式を適用する。
規約：quasicategory 性は不要。使われ方：制限後の単位の回収。 -/
lemma FunctorCompositionTriangle.hom_eq {A X : SSet.{u}} {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W} {d : SSet.Homotopy U W}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHom_comp_eq_of_square l d r Q.diagram Q.bottom Q.top Q.left Q.right

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
