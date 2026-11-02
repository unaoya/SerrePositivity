module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FixedBaseHomotopyFiber
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwiseHomotopyPoint

/-!
概要：fiberwise path の全円柱は元の底固定円柱の同じ fiber 制限を回収する。
方針：path 射影・curry の往復・積の入れ替えを計算する。
規約：全時刻の厳密な等式。使われ方：模型比較の実際の path 座標の識別。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- fiberwise path の fiber 制限を全円柱に戻すと元の同じ底固定円柱になる。 -/
lemma fiberwiseHomotopyPoint_fiber_cylinder {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) {f g : A ⟶ E} (hf : f ≫ p = a) (hg : g ≫ p = a)
    (H : SSet.Homotopy f g) (hH : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a) (b : B _⦋0⦌) :
    (β_ (vertexFiber a b) (Δ[1] : SSet.{u})).hom ≫
      uncurry (vertexFiberι a b ≫ fiberwiseHomotopyPoint p a H hH ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B)) =
    (fixedBaseHomotopyFiber a p hf hg H hH b).h ≫ vertexFiberι p b := by
  rw [fiberwiseHomotopyPoint_path, uncurry_natural_left, uncurry_curry,
    fixedBaseHomotopyFiber_h_ι]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
