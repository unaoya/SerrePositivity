module

public import SerrePositivity.InfinityCategories.F1.StdSimplexFiberFullyFaithful
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：標準単体上の射の同じ fiber にある頂点間の写像空間の比較。
方針：fiber の包含の充満忠実性と、写像空間への作用の合成則を組み合わせる。
規約：fiber 間の比較は共通基底を厳密に保つ射から誘導する。
使われ方：Kerodon Proposition 5.1.6.7、区間上の全空間比較の同じ端点の部分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 概要：標準単体上の fiber の比較が充満忠実なら、その fiber の頂点間の全空間の比較も同値。
方針：包含と比較射の二通りの合成を写像空間で比較し、同値の二つから三つ目を得る性質を使う。
規約：他の fiber にある頂点との写像空間については主張しない。
使われ方：Kerodon Proposition 5.1.6.7、区間上の同じ端点の頂点間の充満忠実性。 -/
lemma pinchedHomMap_equivalence_of_vertexFiberMap_fullyFaithful
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F] {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) (q : F ⟶ Δ[n]) (f : E ⟶ F) (hf : f ≫ q = p)
    (b : (Δ[n] : SSet.{u}) _⦋0⦌)
    (hb : IsFullyFaithful (vertexFiberMap p q f hf b))
    (x y : (vertexFiber p b) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f x.val y.val) := by
  let g := vertexFiberMap p q f hf b
  have hi := vertexFiberι_stdSimplex_isFullyFaithful p b
  have hj := vertexFiberι_stdSimplex_isFullyFaithful q b
  have hc := (hb.comp hj) x y
  have he : vertexFiberι p b ≫ f = g ≫ vertexFiberι q b :=
    (vertexFiberMap_ι p q f hf b).symm
  have hcomp : pinchedHomMap (vertexFiberι p b) x y ≫ pinchedHomMap f x.val y.val =
      pinchedHomMap g x y ≫ pinchedHomMap (vertexFiberι q b)
        (g.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) y) := by
    calc
      _ = pinchedHomMap (vertexFiberι p b ≫ f) x y :=
        (pinchedHomMap_comp (vertexFiberι p b) f x y).symm
      _ = pinchedHomMap (g ≫ vertexFiberι q b) x y := by
        cases he
        rfl
      _ = _ := pinchedHomMap_comp g (vertexFiberι q b) x y
  have hci : IsQCatEquivalence (pinchedHomMap (vertexFiberι p b) x y ≫
      pinchedHomMap f x.val y.val) := by
    rw [hcomp]
    rw [← pinchedHomMap_comp]
    exact hc.isQCatEquivalence
  exact ((hi x y).isQCatEquivalence.cancel_left hci).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
