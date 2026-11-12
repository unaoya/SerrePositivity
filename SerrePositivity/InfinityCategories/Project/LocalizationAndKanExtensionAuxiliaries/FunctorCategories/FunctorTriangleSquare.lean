module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square

/-!
概要：合成三角形に退化三角形を貼り、下辺が恒等の関手正方形を作る。
方針：対角辺を共有する二つの三角形の pushout を用いる。
規約：与えられた三辺のホモトピー代表を厳密に保持する。
使われ方：運んだ単位合成三角形から comma の正方形を復元する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：左上の三角形の後辺は正方形の上辺。
方針：Yoneda で標準単体の有限順序写像を計算する。
規約：三角形の番号は Core.Square に従う。
使われ方：貼り合わせた正方形の上辺を回収する。 -/
lemma triangleSquare_upper_top :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 = SSet.ι₁ := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：左上の三角形の前辺は正方形の左辺。
方針：Yoneda で標準単体の有限順序写像を計算する。
規約：左辺の向きは下から上。
使われ方：単位の代表を回収する。 -/
lemma triangleSquare_upper_left :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：右下の三角形の後辺は正方形の右辺。
方針：Yoneda で標準単体の有限順序写像を計算する。
規約：右辺の向きは下から上。
使われ方：指定した終辺の代表を回収する。 -/
lemma triangleSquare_lower_right :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：右下の三角形の前辺は正方形の下辺。
方針：Yoneda で標準単体の有限順序写像を計算する。
規約：下辺の向きは左から右。
使われ方：退化した下辺を回収する。 -/
lemma triangleSquare_lower_bottom :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 = SSet.ι₀ := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：ホモトピーの前に恒等を合成する退化三角形の図式。
方針：代表辺の idComp 三角形を Yoneda で読む。
規約：第 0 面と第 1 面は元のホモトピー。
使われ方：合成三角形を正方形へ補完する。 -/
noncomputable def functorIdentityCompositionDiagram {A X : SSet.{u}} {U W : A ⟶ X}
    (d : SSet.Homotopy U W) : (Δ[2] : SSet.{u}) ⟶ (ihom A).obj X :=
  SSet.yonedaEquiv.symm (SSet.Truncated.Edge.CompStruct.idComp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d)).simplex

/-- 概要：退化三角形の後辺は元のホモトピー。
方針：idComp 三角形の第 0 面を計算する。
規約：厳密な射の等式。
使われ方：正方形の右辺の認識。 -/
lemma functorIdentityCompositionDiagram_face_zero {A X : SSet.{u}} {U W : A ⟶ X}
    (d : SSet.Homotopy U W) :
    stdSimplex.δ (0 : Fin 3) ≫ functorIdentityCompositionDiagram d = curry d.h := by
  apply SSet.yonedaEquiv.injective
  rw [functorIdentityCompositionDiagram, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact (SSet.Truncated.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d)).d₀

/-- 概要：退化三角形の対角辺は元のホモトピー。
方針：idComp 三角形の第 1 面を計算する。
規約：厳密な射の等式。
使われ方：二つの三角形の貼り合わせ条件。 -/
lemma functorIdentityCompositionDiagram_face_one {A X : SSet.{u}} {U W : A ⟶ X}
    (d : SSet.Homotopy U W) :
    stdSimplex.δ (1 : Fin 3) ≫ functorIdentityCompositionDiagram d = curry d.h := by
  apply SSet.yonedaEquiv.injective
  rw [functorIdentityCompositionDiagram, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact (SSet.Truncated.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d)).d₁

/-- 概要：退化三角形の前辺は始点の恒等辺。
方針：idComp 三角形の第 2 面と一次の定値単体を比較する。
規約：厳密な射の等式。
使われ方：正方形の退化した下辺の認識。 -/
lemma functorIdentityCompositionDiagram_face_two {A X : SSet.{u}} {U W : A ⟶ X}
    (d : SSet.Homotopy U W) :
    stdSimplex.δ (2 : Fin 3) ≫ functorIdentityCompositionDiagram d =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  apply SSet.yonedaEquiv.injective
  rw [functorIdentityCompositionDiagram, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact (SSet.Truncated.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d)).d₂.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)).symm

/-- 概要：下辺が恒等で、他の三辺が指定ホモトピーである関手正方形。
方針：正方形の図式と四辺の制限公式を保持する。
規約：辺の代表は変更しない。
使われ方：comma の正方形の curry 表示の逆。 -/
structure FunctorCompositionSquare {A X : SSet.{u}} {U V W : A ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W) (d : SSet.Homotopy U W) where
  diagram : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X
  bottom : SSet.ι₀ ≫ diagram = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)
  top : SSet.ι₁ ≫ diagram = curry r.h
  left : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ diagram = curry l.h
  right : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ diagram = curry d.h

/-- 概要：合成三角形を指定三辺を保持する関手正方形へ補完する。
方針：対角辺に沿って恒等合成の退化三角形を貼り合わせる。
規約：quasicategory 性を追加仮定せず、入力三角形そのものを使う。
使われ方：逆向きの比較で comma の正方形を構成する。 -/
noncomputable def functorSquareOfCompositionTriangle {A X : SSet.{u}} {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W} {d : SSet.Homotopy U W}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) : FunctorCompositionSquare l r d := by
  have h : stdSimplex.δ (1 : Fin 3) ≫ T.diagram =
      stdSimplex.δ (1 : Fin 3) ≫ functorIdentityCompositionDiagram d := by
    rw [T.face_one, functorIdentityCompositionDiagram_face_one]
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc T.diagram (functorIdentityCompositionDiagram d) h
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ Q = T.diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ Q = functorIdentityCompositionDiagram d :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · rw [← triangleSquare_lower_bottom, Category.assoc, h₁,
      functorIdentityCompositionDiagram_face_two]
  · rw [← triangleSquare_upper_top, Category.assoc, h₀, T.face_zero]
  · rw [← triangleSquare_upper_left, Category.assoc, h₀, T.face_two]
  · rw [← triangleSquare_lower_right, Category.assoc, h₁,
      functorIdentityCompositionDiagram_face_zero]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
