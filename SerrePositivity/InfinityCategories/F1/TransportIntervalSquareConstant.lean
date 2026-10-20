module

public import SerrePositivity.InfinityCategories.F1.TransportIntervalSquareComposition

/-!
概要：四角形の最終辺が定値の場合、二段輸送と直接輸送を全パラメーターで比較する。
方針：定値の底を被覆する同じ始点の定値 prism を使い、四角形の比較から最後の輸送を消す。
規約：動く始点を任意の全パラメーターで保つ。
使われ方：右 Hom の合成四角形の定値辺を取り除き、合成の輸送則を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底の区間族が定値なら、動く始点の対角輸送は同じ始点の族と同型。 -/
def diagonalFiberTransport_constantIso {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a) :
    FunctorIso (diagonalFiberTransport p f c) f := by
  let W := snd (Δ[1] : SSet.{u}) P ≫ f ≫ vertexFiberι p a
  have hW (i : Fin 2) : prismEndpoint i P ≫ W = f ≫ vertexFiberι p a := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hp : W ≫ p = intervalMappingUncurry c := by
    dsimp only [W]
    rw [Category.assoc, Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const, hc]
  exact (leftFibrationPrism_transportIntervalIso p f f c W (hW 0) (hW 1) hp).symm

/-- 最終辺が定値である同じ四角形では、二段輸送は直接の残りの辺の輸送と同型。 -/
def TransportIntervalSquare.constantTopIso {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b d d) (f : P ⟶ vertexFiber p a)
    (hs : intervalMappingUncurry s.top = SSet.const d) :
    FunctorIso (diagonalFiberTransport p (diagonalFiberTransport p f s.bottom) s.right)
      (diagonalFiberTransport p f s.left) :=
  s.transportIso p f ≪≫ diagonalFiberTransport_constantIso p
    (diagonalFiberTransport p f s.left) s.top hs

end SerrePositivity.InfinityCategories
