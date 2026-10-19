module

public import SerrePositivity.InfinityCategories.F1.RelativeBoundaryFamilyEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalTransportBoundaryComparison

/-!
概要：分類図式と境界も動く族全体における輸送円柱比較の同値性。
方針：共通の端点図式の単射性と一般の相対境界族の同値判定を使う。
規約：各固定図式の比較だけでなく実際の族全体の射について結論する。
使われ方：区間の表現空間の境界 fiber へ円柱の可縮性を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間上の輸送円柱比較は分類図式と端点写像を動かす族全体でも同値。
方針：実際の比較の前合成同値性と共通境界の単射性を族の比較へ適用する。
規約：パラメーター L は任意の quasicategory、データの族 d も任意。
使われ方：両端固定の区間写像空間上に実際の比較を束ねる主要界面。 -/
lemma intervalTransportCylinder_boundaryFamily_isQCatEquivalence
    {E L : SSet.{u + 1}} [Quasicategory L]
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) :
    let c := pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁
    let j := transportCylinderEndpointInclusion f
    letI : Mono (j ≫ c) := transportCylinderEndpoint_comparison_mono p f H h₀ h₁
    letI : Mono j := mono_of_mono j c
    let rA := Functor.PullbackObjObj.ofHasPullback internalHom (j ≫ c) pointedSpaceProjection
    let rD := Functor.PullbackObjObj.ofHasPullback internalHom j pointedSpaceProjection
    ∀ d : L ⟶ rA.pt,
      IsQCatEquivalence (relativeBoundaryFamilyPre c j pointedSpaceProjection rA rD d) := by
  intro c j rA rD d
  let : Mono (j ≫ c) := transportCylinderEndpoint_comparison_mono p f H h₀ h₁
  let : Mono j := mono_of_mono j c
  exact relativeBoundaryFamilyPre_isQCatEquivalence c
    (intervalTransportCylinder_isPrecompositionEquivalence p f H h₀ h₁ hp) j
    pointedSpaceProjection rA rD d

end SerrePositivity.InfinityCategories
