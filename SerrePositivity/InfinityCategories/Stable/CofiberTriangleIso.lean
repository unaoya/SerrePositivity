module
public import SerrePositivity.InfinityCategories.Stable.CofiberTriangle
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.Stable.CofiberComparisonExt

/-! # Cofiber 三角形の比較同型

概要：同型な cofiber 図式から得る三角形は同型であり、同じ第一辺の二つの列にも適用できる。
方針：可逆な図式辺の三成分が可逆であることを評価関手で確認する。
規約：三角圏の公理を仮定しない。使われ方：逆回転の代表と元の列の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cofiber 四角形間の関手同型は、それらの cofiber 三角形の同型を与える。
方針：実際の可逆ホモトピーから作った三角形の射を三成分の可逆性で同型と認証する。
規約：構成済みの接続射と整数シフトを使う。使われ方：cofiber 代表の変更。 -/
def cofiberTriangleIsoOfFunctorIso {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (e : FunctorIso t.square d.square) : cofiberTriangle t ht ≅ cofiberTriangle d hd := by
  let Q := e.simplicialHomotopy
  let m := cofiberTriangleMapOfHomotopy t d ht hd Q
  have hQ : IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy Q)) := by
    dsimp only [Q, FunctorIso.simplicialHomotopy]
    rw [stableFunctorEdge_homotopy_roundtrip, FunctorIso.edge_homMk]
    infer_instance
  have he (i j : Fin 2) : IsIso ((homotopyNatTransOfEndpoints Q.h Q.h₀ Q.h₁).app
      (SSet.HomotopyCategory.mk (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i j))) := by
    have hh := homotopyEvaluationOfEndpoints_arrow Q
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i j)
    have hi := (hoFunctor.map (evaluateFunctorAt (Y := X)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i j))).toFunctor.map_isIso
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy Q))
    exact (congrArg (fun a : Arrow (hoFunctor.obj X) => IsIso a.hom) hh).mp hi
  have h₁ : IsIso m.hom₁ := he 0 0
  have h₂ : IsIso m.hom₂ := he 1 0
  have h₃ : IsIso m.hom₃ := he 1 1
  have : IsIso m := Triangle.isIso_of_isIsos m h₁ h₂ h₃
  exact asIso m

/-- 概要：第一辺が単体的な射として同じ二つの cofiber 列の三角形は同型。
方針：同じ辺の二つの CofiberSquare として図式同型を構成し、三角形へ移す。
規約：零角や cofiber 頂点の選択は異なってよい。使われ方：逆回転の像の比較。 -/
lemma nonempty_cofiberTriangleIso_of_bottom_eq {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t d : ZeroTriangle X) (ht : IsCofiberSequence t) (hd : IsCofiberSequence d)
    (h : squareBottomEdge ≫ t.square = squareBottomEdge ≫ d.square) :
    Nonempty (cofiberTriangle t ht ≅ cofiberTriangle d hd) := by
  let s : CofiberSquare (squareBottomArrow t.square) := {
    square := t.square
    zero_corner := t.zero_corner
    bottom_edge := (by
      rw [squareBottomArrow_edge]
      exact (SSet.yonedaEquiv.symm_apply_apply _).symm)
    isPushout := ht }
  let r : CofiberSquare (squareBottomArrow t.square) := {
    square := d.square
    zero_corner := d.zero_corner
    bottom_edge := (by
      rw [← h, squareBottomArrow_edge]
      exact (SSet.yonedaEquiv.symm_apply_apply _).symm)
    isPushout := hd }
  obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso s r
  exact ⟨cofiberTriangleIsoOfFunctorIso t d ht hd e⟩

end SerrePositivity.InfinityCategories
