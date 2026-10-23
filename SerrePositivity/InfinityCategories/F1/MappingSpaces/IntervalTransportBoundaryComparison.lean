module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalTransportBoundary
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBoundaryComparison

/-!
概要：輸送円柱比較は底の分類図式と両端写像を厳密に固定しても同値を誘導する。
方針：両端の包含の一致から単射性を得て、境界固定の相対関手空間の比較を適用する。
規約：比較射そのものの単射性は不要。
使われ方：Kerodon Lemma 5.6.9.1 の円柱側の可縮な fiber を区間側へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：輸送円柱の境界を全空間へ写した射は単射。
方針：実際の両端 fiber の包含と一致することを使う。
規約：輸送 prism の始点と終点を厳密に指定する。
使われ方：境界固定の相対関手空間の二つの制限の充填性。 -/
lemma transportCylinderEndpoint_comparison_mono {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    Mono (transportCylinderEndpointInclusion f ≫
      pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁) := by
  rw [transportCylinderEndpointInclusion_comparison p f H h₀ h₁]
  infer_instance

/-- 概要：底の図式と両端写像を固定した輸送円柱への制限は同値。
方針：全空間の前合成同値と両端包含の単射性を境界固定の一般比較へ渡す。
規約：底の分類図式 d と境界の相対関手の頂点 b は任意。
使われ方：区間上の実際の表現空間の境界 fiber の比較。 -/
lemma intervalTransportCylinder_boundary_isQCatEquivalence {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) (d : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}) :
    let c := pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁
    let j := transportCylinderEndpointInclusion f
    letI : Mono (j ≫ c) := transportCylinderEndpoint_comparison_mono p f H h₀ h₁
    letI : Mono j := mono_of_mono j c
    ∀ b : (relativeFunctorSpace pointedSpaceProjection ((j ≫ c) ≫ (p ≫ d))) _⦋0⦌,
      IsQCatEquivalence (vertexFiberMap
        (relativeFunctorPre pointedSpaceProjection (p ≫ d) (j ≫ c))
        (relativeFunctorPre pointedSpaceProjection (c ≫ (p ≫ d)) j)
        (relativeFunctorPre pointedSpaceProjection (p ≫ d) c)
        (relativeFunctorPre_comp pointedSpaceProjection (p ≫ d) c j) b) := by
  intro c j b
  let : Mono (j ≫ c) := transportCylinderEndpoint_comparison_mono p f H h₀ h₁
  let : Mono j := mono_of_mono j c
  exact relativeFunctorBoundaryMap_isQCatEquivalence pointedSpaceProjection (p ≫ d) c
    (intervalTransportCylinder_isPrecompositionEquivalence p f H h₀ h₁ hp) j b

/-- 概要：分類図式と両端写像を固定した lift 空間の可縮性は輸送円柱比較で保ち反映される。
方針：両端の単射性を固定境界比較の可縮性不変性へ適用する。
規約：分類図式そのものも両端の写像も厳密に固定する。
使われ方：円柱側の境界延長の可縮な選択を区間上の全空間へ戻す。 -/
lemma intervalTransportCylinder_boundary_isContractibleKan_iff {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) (d : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}) :
    let c := pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁
    let j := transportCylinderEndpointInclusion f
    ∀ b : (relativeFunctorSpace pointedSpaceProjection ((j ≫ c) ≫ (p ≫ d))) _⦋0⦌,
      IsContractibleKan (vertexFiber
        (relativeFunctorPre pointedSpaceProjection (p ≫ d) (j ≫ c)) b) ↔
        IsContractibleKan (vertexFiber
          (relativeFunctorPre pointedSpaceProjection (c ≫ (p ≫ d)) j) b) := by
  intro c j b
  let : Mono (j ≫ c) := transportCylinderEndpoint_comparison_mono p f H h₀ h₁
  let : Mono j := mono_of_mono j c
  exact relativeFunctorBoundary_isContractibleKan_iff pointedSpaceProjection (p ≫ d) c
    (intervalTransportCylinder_isPrecompositionEquivalence p f H h₀ h₁ hp) j b

end SerrePositivity.InfinityCategories
