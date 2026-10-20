module

public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostcompositionVertices
public import SerrePositivity.InfinityCategories.F1.PullbackNerveFiber

/-!
概要：底の頂点表示を変更しても、同じ可換正方形の対角輸送の自然性を保つ。
方針：元の自然性に fiber の等号輸送を合成し、区間族の端点も同じ等号で正規化する。
規約：元の動く始点と全パラメーターを保ち、新たな輸送は選ばない。
使われ方：unstraightening の fiber 同型と標準 Kan 頂点での pointed 輸送の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 正方形による対角輸送の比較を、指定した標準頂点の表示へ厳密に正規化する。 -/
def diagonalFiberTransport_squareOfEqIso {P E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} {a' b' : D _⦋0⦌}
    (ha : g.app _ a = a') (hb : g.app _ b = b')
    (x : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) :
    FunctorIso
      (diagonalFiberTransport p x c ≫ transportSquareFiberMap p q f g h b ≫
        eqToHom (congrArg (vertexFiber q) hb))
      (diagonalFiberTransport q
        (x ≫ transportSquareFiberMap p q f g h a ≫
          eqToHom (congrArg (vertexFiber q) ha))
        (c ≫ intervalMappingPostOfEq g a b ha hb)) := by
  subst a'
  subst b'
  have hc : intervalMappingPostOfEq g a b rfl rfl = intervalMappingPost g a b := by
    apply intervalMappingUncurry_injective _ _
    rw [intervalMappingPostOfEq, intervalMappingUncurry_curryOfEndpoints,
      intervalMappingPost_universal_uncurry]
  simpa only [hc, eqToHom_refl, Category.comp_id] using
    diagonalFiberTransport_squareIso p q f g h x c

end SerrePositivity.InfinityCategories
