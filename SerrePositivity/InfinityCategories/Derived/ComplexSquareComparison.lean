module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareHomEvaluation
public import SerrePositivity.InfinityCategories.Stable.ObjectEqualityTransport

/-! # 複体四角形の前合成・後合成の合成比較

概要：中央四角形の同定を挟んだ比較を構成し、両端の成分を指定した鎖写像に同定する。
方針：各因子の Arrow 等式を使い、恒等成分と中央の対象輸送を打ち消す。
規約：余極限性や零複体は不要。使われ方：D7 の suspension 比較の成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {A A' B C D D' : Complex S}
variable (s : ComplexSquareData A B C D) (t : ComplexSquareData A' B C D')
/-- 前合成と後合成の中央四角形を同定して得る、四角形全体の h の射。 -/
def comparisonHom (p : A ⟶ A') (q : D ⟶ D') (h : s.postcompose q = t.precompose p) :
    (SSet.HomotopyCategory.mk (functorVertex s.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S)))) ⟶
        SSet.HomotopyCategory.mk (functorVertex t.square) :=
  SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSquareEdge q) ≫
    chosenEqToHom (congrArg (fun k : ComplexSquareData A B C D' =>
      SSet.HomotopyCategory.mk (functorVertex k.square)) h) ≫
    SSet.Truncated.HomotopyCategory.homMk (t.precomposeSquareEdge p)
/-- 合成比較の始点成分は前合成射 p。 -/
lemma comparisonHom_source_arrow (p : A ⟶ A') (q : D ⟶ D')
    (h : s.postcompose q = t.precompose p) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (s.comparisonHom t p q h)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge p).toTruncated) := by
  unfold comparisonHom
  exact (arrowMk_map_chosenTransport_comp_of_left_identity
    (squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0) _ _ _
    (s.postcomposeHom_source_arrow q)).trans (t.precomposeHom_source_arrow p)
/-- 合成比較の終点成分は後合成射 q。 -/
lemma comparisonHom_target_arrow (p : A ⟶ A') (q : D ⟶ D')
    (h : s.postcompose q = t.precompose p) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (s.comparisonHom t p q h)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge q).toTruncated) := by
  unfold comparisonHom
  exact (arrowMk_map_chosenTransport_comp_of_right_identity
    (squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1) _ _ _
    (t.precomposeHom_target_arrow p)).trans (s.postcomposeHom_target_arrow q)
end SerrePositivity.InfinityCategories.ComplexSquareData
