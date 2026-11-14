module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-!
概要：関手区間を値とする実四角形を、四角形の関手圏の比較辺へ移す。
方針：二変数の交換を全単体で行い、各角で同じ元の区間辺を回収する。
規約：極限・余極限・安定性を仮定しない。
使われ方：回転した cofiber 族と懸垂図式族の比較の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：四角形の区間族を同じ全単体の区間上の四角形族へ交換する。
方針：内部 Hom の反変随伴の同じ転置を使う。
規約：元の四角形族を保持する。使われ方：比較辺の構成。 -/
def intervalSquareFamily {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) Δ[1] X R

/-- 概要：交換した族の区間頂点は元の同じ四角形の全評価。
方針：反変随伴の頂点での評価式を使う。
規約：両端以外の全頂点にも成り立つ。
使われ方：比較辺の両端の普遍性の読み戻し。 -/
lemma intervalSquareFamily_vertex {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (a : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (intervalSquareFamily R).app (Opposite.op ⦋0⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero R a

/-- 概要：交換した区間族を元の四角形変数へ戻すと元の関手頂点になる。
方針：二回の転置が元に戻ることを使う。
規約：ホモトピーでなく厳密等式。使われ方：全角の比較辺の評価。 -/
lemma intervalSquareFamily_swap_vertex {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso Δ[1] (Δ[1] ⊗ Δ[1]) X).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (intervalSquareFamily R)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[1] (Δ[1] ⊗ Δ[1]) X
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) Δ[1] X R)) = _
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) Δ[1] X).left_inv R)

/-- 概要：比較辺を各角で評価すると、元の関手区間の同じ辺に一致する。
方針：内部 Hom の交換の区間辺の評価式へ二重転置を代入する。
規約：端点の表示を除いた実一次単体の等式。
使われ方：cofiber と懸垂の比較の可逆性の輸送。 -/
lemma intervalSquareFamily_edge_evaluate {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (intervalSquareFamily R))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (R.app (Opposite.op ⦋0⦌) k) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_interval_evaluate (Δ[1] ⊗ Δ[1]) X
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (intervalSquareFamily R)) k
  rw [intervalSquareFamily_swap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h
  exact h.symm

/-- 概要：四角形の区間族の比較を指定した実両端を持つ辺にする。
方針：元の族の一次単体を保ち、区間の二頂点で両端を同定する。
規約：両端は元の評価四角形そのもの。
使われ方：cofiber 四角形間の可逆性判定。 -/
def intervalSquareComparisonEdge {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) where
  edge := SSet.yonedaEquiv (intervalSquareFamily R)
  src_eq := by
    change ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X).δ 1
      (SSet.yonedaEquiv (intervalSquareFamily R)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [SSet.yonedaEquiv_comp]
    have hv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    rw [hv]
    exact intervalSquareFamily_vertex R (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  tgt_eq := by
    change ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X).δ 0
      (SSet.yonedaEquiv (intervalSquareFamily R)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [SSet.yonedaEquiv_comp]
    have hv : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    rw [hv]
    exact intervalSquareFamily_vertex R (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：指定両端の比較辺の各角で元の区間辺を回収する。
方針：全族の評価式を同じ Yoneda 表示へ戻す。
規約：辺の実一次単体を保つ。使われ方：比較の成分の可逆性。 -/
lemma intervalSquareComparisonEdge_evaluate {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (i j : Fin 2) :
    ((intervalSquareComparisonEdge R).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) i j)))).edge =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R i j) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) i j)).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (intervalSquareFamily R)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex]
  exact intervalSquareFamily_edge_evaluate R _

/-- 概要：比較辺の各角の可逆性は元の同じ区間辺の可逆性と同値。
方針：実一次単体の評価式を端点つき辺の判定へ移す。
規約：端点を推測する追加の選択は不要。
使われ方：cofiber と懸垂の比較の成分判定。 -/
lemma intervalSquareComparisonEdge_isInvertible_evaluate_iff {X : SSet.{u}}
    [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((intervalSquareComparisonEdge R).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) i j)))) ↔
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R i j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((intervalSquareComparisonEdge R).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) i j)))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R i j))).edge from
      intervalSquareComparisonEdge_evaluate R i j)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
