module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices

/-!
概要：元の相対評価の指定同型を、底と実際の評価写像の等式で厳密に移送する。
方針：全ての等式を消去し、相対頂点の可換性の証明無関係性を使う。
規約：同型を選び直さない。使われ方：元の weighted 係数の評価比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の底と両評価の表示を揃えても、指定された相対同型そのものを保持する。 -/
def relativeEvaluationIsoOfEq {A E B : SSet.{u}} {p : E ⟶ B} {a b : A ⟶ B}
    {v v' w w' : A ⟶ E} (hab : a = b) (hv : v = v') (hw : w = w')
    {hva : v ≫ p = a} {hwa : w ≫ p = a} {hvb : v' ≫ p = b} {hwb : w' ≫ p = b}
    (e : VertexIso (relativeFunctorVertex p a v hva) (relativeFunctorVertex p a w hwa)) :
    VertexIso (relativeFunctorVertex p b v' hvb) (relativeFunctorVertex p b w' hwb) := by
  subst b v' w'
  exact e

end SerrePositivity.InfinityCategories.F2.Ind
