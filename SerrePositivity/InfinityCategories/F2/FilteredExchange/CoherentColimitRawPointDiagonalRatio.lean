module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawPointDiagonal
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalPointDiagonalRatio
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismLeftValueRatio
/-!
概要：raw 指定対角値の比を、同じ指定点の普遍比較による比へ戻す。
方針：native 終点の指定点表示を先に固定し、頂点同型の合成を表示変更する。
規約：元の raw 辺・全初期値・指定値を保持する。
使われ方：Ncomp の最後辺の比と元の作用比較の照合。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (b : SSet.Homotopy G J)
local notation "p" => pointedSpaceProjection
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "y" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "n" => Equiv.symm (functorVertexEquiv _ _)
  (NatTrans.app (parametrizedFiberTransport p x y) (Opposite.op ⦋0⦌)
    (NatTrans.app A (Opposite.op ⦋0⦌) l))
/-- 概要：同じ実 native 終点の指定点表示。方針：零頂点の Yoneda 評価を計算。
規約：元の区間頂点と値射を保持。使われ方：raw 比の終点表示。 -/
lemma coherentColimitRawPointDiagonal_native_at_yoneda {K Z : SSet.{u + 1}}
    (q : K ⟶ vertexFiber p x) (v₂ : vertexFiber p y ⟶ Z) :
    diagonalFiberTransport p q (intervalMappingCurryOfEndpoints
      (intervalMappingUncurry (SSet.const (coherentColimitRawIntervalVertex B b) : K ⟶ _))
      (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)) ≫ v₂ =
      (q ≫ n) ≫ v₂ := by
  let v : K ⟶ intervalMappingSpace x y := SSet.const (coherentColimitRawIntervalVertex B b)
  have hv : NatTrans.app A (Opposite.op ⦋0⦌) l = coherentColimitRawIntervalVertex B b := by
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  have ht : diagonalFiberTransport p q (intervalMappingCurryOfEndpoints (intervalMappingUncurry v)
      (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)) ≫ v₂ =
      (q ≫ n) ≫ v₂ := by
    have hd := congrArg (fun k => k ≫ v₂) (coherentColimitRawPointDiagonal_native B b q)
    have hn := congrArg (fun z => (q ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport p x y).app (Opposite.op ⦋0⦌) z)) ≫ v₂) hv
    exact hd.trans hn.symm
  exact ht
/-- 概要：同じ実 raw 比を一般の指定区間の比へ移す。
方針：同じ実 prism と両端を保持。規約：左因子を保持。使われ方：raw 比の照合。 -/
lemma coherentColimitRawPointDiagonal_ratio_heq_pointed {K Y Z : SSet.{u + 1}}
    (q : K ⟶ vertexFiber p x) (v₁ : vertexFiber p x ⟶ Y) (v₂ : vertexFiber p y ⟶ Z) (g : Y ⟶ Z)
    (e : FunctorIso (coherentColimitRawFiberTransport B b ≫ v₂) (v₁ ≫ g)) :
    HEq ((functorIsoOfEq (e.precomp q)
          (Category.assoc q (coherentColimitRawFiberTransport B b) v₂).symm rfl).symm ≪≫
        (coherentColimitRawPointDiagonalComparison B b q).postcomp v₂)
      (pointedIntervalPointDiagonalValueRatio A l q v₁ v₂ g e) := by
  apply diagonalTransportIso_left_postcomp_heq_of_prism
  rfl
end
end SerrePositivity.InfinityCategories.F2
