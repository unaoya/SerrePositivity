module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeEquivalencePathExtension
public import SerrePositivity.InfinityCategories.F1.InvertibleFunctorEdgePath

/-!
概要：指定した可逆 path を保ち、同型で可換な関手正方形を厳密に可換にする。
方針：終点と標的の path を固定して相対 path を持ち上げ、零端点を取る。
規約：別の標的 path へ選び直さない。持ち上げ性は証明を明示的に受け取る。
使われ方：同じ cospan の局所比較を pullback 比較へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 指定した標的 path と終点を厳密に保つ、全パラメーターの相対 path 持ち上げ。 -/
lemma exists_functorSquarePathLift {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) (hq : F1B.KanEquivalenceLifting q)
    (f : A ⟶ E) (P : A ⟶ equivalencePath B)
    (hP : P ≫ equivalencePathEndpoint B 1 = f ≫ q) :
    ∃ L : A ⟶ equivalencePath E,
      L ≫ equivalencePathMap q = P ∧ L ≫ equivalencePathEndpoint E 1 = f := by
  obtain ⟨L, _, hL, hLf⟩ := F1B.exists_kanRelativeEquivalencePath_extension q hq
    (initial.to A) (initial.to (equivalencePath E)) P f
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _) hP
  exact ⟨L, hL, hLf⟩

/-- 同じ標的 path を持ち上げた零端点は、指定された標的の零端点へ厳密に写る。 -/
lemma functorSquarePathLift_zero {A E B : SSet.{u}} (q : E ⟶ B)
    (L : A ⟶ equivalencePath E) (P : A ⟶ equivalencePath B)
    (hL : L ≫ equivalencePathMap q = P) :
    (L ≫ equivalencePathEndpoint E 0) ≫ q = P ≫ equivalencePathEndpoint B 0 := by
  rw [Category.assoc, ← equivalencePathMap_endpoint, ← Category.assoc, hL]

/-- 関手同型で可換な正方形を、元の成分と同型な成分で厳密に可換にできる。 -/
lemma exists_functorSquare_strictification {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) (hq : F1B.KanEquivalenceLifting q)
    (f : A ⟶ E) (g : A ⟶ B) (e : FunctorIso g (f ≫ q)) :
    ∃ (f' : A ⟶ E) (L : A ⟶ equivalencePath E),
      f' ≫ q = g ∧ L ≫ equivalencePathEndpoint E 0 = f' ∧
      L ≫ equivalencePathEndpoint E 1 = f ∧
      L ≫ equivalencePathMap q =
        invertibleFunctorEdgePath (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) := by
  let P := invertibleFunctorEdgePath (FunctorIso.edge e) (FunctorIso.edge_isInvertible e)
  obtain ⟨L, hL, hLf⟩ := exists_functorSquarePathLift q hq f P
    (invertibleFunctorEdgePath_one _ _)
  refine ⟨L ≫ equivalencePathEndpoint E 0, L, ?_, rfl, hLf, hL⟩
  exact (functorSquarePathLift_zero q L P hL).trans (invertibleFunctorEdgePath_zero _ _)

end SerrePositivity.InfinityCategories
