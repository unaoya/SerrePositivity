module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairAdjointFunctor

/-!
概要：合成した実関手の同型を元の頂点の合成の表示で評価する。
方針：抽象的な三つの射の段階で評価成分を構成して不透明な実装に保持する。
規約：実際の成分を構成しており、新しい公理や存在仮定ではない。
使われ方：構成した随伴関手の複雑な値に対する型の正規化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：同じ合成関手の全自然同型から、元の二つの頂点の実同型を回収する。
方針：既存の評価成分を抽象的な射の段階で構成する。
規約：全自然な比較の同じ成分を保持し、頂点同型を別に選ばない。
使われ方：元の全単位族との Yoneda 比較の評価。 -/
opaque pairCompositeFunctorIsoVertex {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory X]
    {f : A ⟶ B} {g : B ⟶ X} {h : A ⟶ X}
    (e : FunctorIso (f ≫ g) h) (v : A _⦋0⦌) :
    VertexIso (g.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) v))
      (h.app (Opposite.op ⦋0⦌) v) := e.app v

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
