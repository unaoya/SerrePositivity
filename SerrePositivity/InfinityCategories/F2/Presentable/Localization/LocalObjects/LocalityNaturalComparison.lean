module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.LocalityInversion
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftTransportComponents

/-!
概要：同じ局所性を全共変 Hom 関手の自然比較成分の可逆性で判定する。
方針：共同 Hom の反変変数の辺作用を評価し、元の表現可能前層の辺作用と同定する。
規約：同じ指定辺から一つの全自然比較を作る。
使われ方：局所性の filtered 余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
open HomotopyLimits

/-- 概要：指定辺による元の全共変 Hom 関手間の反変な自然比較。
方針：元の co-Yoneda で反対辺を写し、両端を元の共変 Hom へ正規化する。
規約：全関手圏の二胞体を使用する。
使われ方：全パラメータでの局所性比較。 -/
def localPrecompositionComparison {C : SSet.{u}} [Quasicategory C] {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y) :
    FunctorHom (homInfinityCovariant y) (homInfinityCovariant x) :=
  eqToHom (congrArg HomotopyCategory.mk (coyonedaInfinityMap_vertex y)).symm ≫
    Truncated.HomotopyCategory.homMk
      (((uliftTruncatedEdge.{u, u + 1} (edgeOp e)).map
        ((truncation 2).map (coyonedaInfinityMap C)))) ≫
      eqToHom (congrArg HomotopyCategory.mk (coyonedaInfinityMap_vertex x))

private lemma normalizedEdgeEvaluation_isIso_iff {K X : SSet.{u}}
    {U V : K ⟶ X} {a b : ((ihom K).obj X) _⦋0⦌}
    (d : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b)
    (ha : a = functorVertex U) (hb : b = functorVertex V) (k : K _⦋0⦌) :
    IsIso (functorHomEvaluate
      (eqToHom (congrArg HomotopyCategory.mk ha).symm ≫
        Truncated.HomotopyCategory.homMk d ≫
        eqToHom (congrArg HomotopyCategory.mk hb)) k) ↔
      IsInvertibleEdge (d.map ((truncation 2).map (evaluateFunctorAt k))) := by
  rw [F1B.kanFunctorHomEvaluate_isIso_iff]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
  rw [isIso_comp_left_iff (eqToHom _) (_ ≫ _),
    isIso_comp_right_iff _ (eqToHom _)]
  rfl

private lemma mappedEdge_evaluation_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {x y : X _⦋0⦌} (d : Truncated.Edge (X := (truncation 2).obj X) x y) :
    IsInvertibleEdge ((d.map ((truncation 2).map f)).map ((truncation 2).map g)) ↔
      IsInvertibleEdge (d.map ((truncation 2).map (f ≫ g))) := by
  rfl

/-- 概要：同じ自然比較の元の対象での可逆性は指定辺の局所性と同値。
方針：評価による端点の同型を消去し、共同 Hom の評価を元の表現可能前層へ戻す。
規約：同じ比較成分と元の局所性を使用する。
使われ方：指定余極限の比較成分の可逆性判定。 -/
lemma localPrecompositionComparison_isIso_iff {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (z : C _⦋0⦌) :
    IsIso (functorHomEvaluate (localPrecompositionComparison e) (ULift.up z)) ↔
      IsLocalForHom (Truncated.HomotopyCategory.homMk e) z := by
  have h := normalizedEdgeEvaluation_isIso_iff
    ((uliftTruncatedEdge.{u, u + 1} (edgeOp e)).map
      ((truncation 2).map (coyonedaInfinityMap C)))
    (coyonedaInfinityMap_vertex y) (coyonedaInfinityMap_vertex x) (ULift.up z)
  have hcomp := mappedEdge_evaluation_comp (coyonedaInfinityMap C)
    (evaluateFunctorAt (ULift.up z)) (uliftTruncatedEdge.{u, u + 1} (edgeOp e))
  rw [coyonedaInfinityMap_evaluation] at hcomp
  exact h.trans (hcomp.trans (isLocalForHom_iff_representableInverts z e).symm)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
