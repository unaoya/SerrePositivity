module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：関手正方形を、元の二単体を保持した二つの合成三角形に分ける。
方針：共通対角辺をホモトピーとして認識し、正方形の三角形包含で制限する。
規約：合成の類から別の三角形を選び直さない。
使われ方：B1 の comma 比較で元の coherence を保つ経路を作る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：正方形の共通対角辺を端点つきの関手の辺とする。
方針：両端を左辺・右辺の端点で認識する。
規約：辺そのものは正方形への対角の制限。
使われ方：二つの三角形に共通のホモトピー代表。 -/
noncomputable def FunctorCompositionSquare.diagonalEdge {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W) where
  edge := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ Q.diagram)
  src_eq := by
    change ((ihom A).obj X).δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ Q.diagram)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal =
        stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    rw [← Category.assoc, hv, Category.assoc, Q.left,
      stdSimplex.yonedaEquiv_δ_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l).src_eq
  tgt_eq := by
    change ((ihom A).obj X).δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ Q.diagram)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have hv : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal =
        stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    rw [← Category.assoc, hv, Category.assoc, Q.right,
      stdSimplex.yonedaEquiv_δ_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d).tgt_eq

/-- 概要：共通対角辺を、指定端点のホモトピーとして読む。
方針：対角の関手の辺を uncurry する。
規約：元の正方形への制限を保持する。
使われ方：二つの実際の合成三角形の共通辺。 -/
noncomputable def FunctorCompositionSquare.diagonal {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) : SSet.Homotopy U W :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge Q.diagonalEdge

/-- 概要：対角のホモトピーを curry すると元の対角の図式になる。
方針：閉構造と Yoneda の両逆。
規約：類でなく射の等式。
使われ方：三角形の対角面の厳密な回収。 -/
lemma FunctorCompositionSquare.diagonal_curry {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    curry Q.diagonal.h = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ Q.diagram := by
  change curry (uncurry (SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ Q.diagram)))) = _
  rw [Equiv.symm_apply_apply, curry_uncurry]

/-- 概要：正方形の左上の二単体は指定二辺と共通対角辺の合成三角形。
方針：三つの面を正方形の左辺・上辺・対角辺で照合する。
規約：図式は元の正方形の制限そのもの。
使われ方：基準単位三角形との相対比較。 -/
noncomputable def FunctorCompositionSquare.upperTriangle {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r Q.diagonal where
  diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ Q.diagram
  face_zero := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_top, Q.top]
  face_one := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal, Q.diagonal_curry]
  face_two := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_left, Q.left]

/-- 概要：関手の恒等辺を表すホモトピー。
方針：関手単体集合の退化辺を uncurry する。
規約：恒等の代表を固定する。
使われ方：正方形の下側の合成三角形の前辺。 -/
noncomputable def identityFunctorHomotopy {A X : SSet.{u}} (U : A ⟶ X) : SSet.Homotopy U U :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))

/-- 概要：恒等ホモトピーの curry は関手の頂点に定値。
方針：退化辺の Yoneda 表示を使う。
規約：射の等式。
使われ方：正方形の下辺を認識する。 -/
lemma identityFunctorHomotopy_curry {A X : SSet.{u}} (U : A ⟶ X) :
    curry (identityFunctorHomotopy U).h = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  change curry (uncurry (SSet.yonedaEquiv.symm
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)).edge)) = _
  rw [curry_uncurry]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)).symm

/-- 概要：正方形の右下の二単体を恒等辺・右辺の合成三角形とする。
方針：下辺・右辺・対角面をそのまま読む。
規約：元の二単体を選び直さず保持する。
使われ方：共通対角辺から右辺へ進む、coherence を保った経路。 -/
noncomputable def FunctorCompositionSquare.lowerTriangle {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (identityFunctorHomotopy U) d Q.diagonal where
  diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ Q.diagram
  face_zero := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_right, Q.right]
  face_one := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal, Q.diagonal_curry]
  face_two := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_bottom, Q.bottom,
    identityFunctorHomotopy_curry]

/-- 概要：恒等辺の後に指定辺を合成する基準三角形。
方針：指定辺の idComp の二単体を使う。
規約：後辺・対角辺は指定辺そのもの。
使われ方：正方形の下側との相対比較の終点。 -/
noncomputable def identityFunctorCompositionTriangle {A X : SSet.{u}} {U W : A ⟶ X}
    (d : SSet.Homotopy U W) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (identityFunctorHomotopy U) d d where
  diagram := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram d
  face_zero := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_zero d
  face_one := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_one d
  face_two := by rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram_face_two, identityFunctorHomotopy_curry]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
