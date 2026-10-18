module

public import SerrePositivity.InfinityCategories.F1B.FunctorRelativeInitial
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.FiberwiseHomotopy

/-!
概要：点ごとに相対始対象である持ち上げから、同じ基底上の任意の族へ射を作る。
方針：内部 Hom の相対境界充填を fiber の始対象性へ制限し、実際の辺を選ぶ。
規約：基底上の一致はホモトピー全体の raw な射について保証する。
使われ方：B1 の comma の単位切断から自然な余単位を取り出す接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対始対象から同じ fiber の任意の頂点へ基底が恒等の辺がある。
方針：相対境界充填から fiber の始対象性を得る。
規約：quasicategory 性や fibration 性は不要。
使われ方：内部 Hom の fiber 内で自然変換を選ぶ。 -/
lemma exists_edge_over_of_initialBoundaryLifting {E B : SSet.{u}} (p : E ⟶ B)
    (x y : E _⦋0⦌) (hx : InitialBoundaryLifting p x)
    (h : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) :
    ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      p.app (Opposite.op ⦋1⦌) k.edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
          (p.app (Opposite.op ⦋0⦌) y)).edge := by
  let b := p.app (Opposite.op ⦋0⦌) y
  let v₀ : (vertexFiber p b) _⦋0⦌ := ⟨x, by rw [pinchedConstant_zero]; exact h⟩
  let v₁ : (vertexFiber p b) _⦋0⦌ := ⟨y, by rw [pinchedConstant_zero]⟩
  obtain ⟨k⟩ := (InitialBoundaryLifting.isInitialVertex_fiber p b v₀ hx).nonempty_edge v₁
  refine ⟨k.map ((truncation 2).map (vertexFiberι p b)), ?_⟩
  change (vertexFiberι p b ≫ p).app (Opposite.op ⦋1⦌) k.edge = _
  rw [vertexFiberι_comp]
  exact pinchedConstant_one b

/-- 概要：点ごとに相対始対象である持ち上げから同じ基底上の任意の族へホモトピーがある。
方針：内部 Hom の相対充填で得た fiber の辺を uncurry する。
規約：始域パラメータは任意。基底への像は時間に定値。
使われ方：単位切断と恒等矢印の族を comma 内で比較して余単位を得る。 -/
lemma exists_homotopy_over_of_pointwise_initialBoundaryLifting {A E B : SSet.{u}}
    (p : E ⟶ B) (f g : A ⟶ E)
    (hf : ∀ a : A _⦋0⦌, InitialBoundaryLifting p (f.app (Opposite.op ⦋0⦌) a))
    (h : f ≫ p = g ≫ p) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ g ≫ p := by
  obtain ⟨k, hk⟩ := exists_edge_over_of_initialBoundaryLifting ((ihom A).map p)
    (functorVertex f) (functorVertex g) (initialBoundaryLifting_ihom_of_pointwise p f hf)
    (by change functorVertex (f ≫ p) = functorVertex (g ≫ p); rw [h])
  refine ⟨simplicialHomotopyOfFunctorEdge k, ?_⟩
  exact simplicialHomotopyOfFunctorEdge_comp_eq_constant p (g ≫ p) k hk

end SerrePositivity.InfinityCategories
