module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalTransportCylinder
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence

/-!
概要：区間上の left fibration の写像円柱への制限による相対関手空間の同値。
方針：全空間の前合成同値を pointed-space 射影への相対前合成に移す。
規約：分類図式を厳密に固定する。
使われ方：Kerodon Lemma 5.6.9.1 の表現空間と prism の中間空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間の分類図式を固定すると写像円柱への相対関手空間の制限は同値。
方針：実際の輸送円柱比較の前合成同値性を相対関手空間へ移す。
規約：比較射の単射性も円柱の quasicategory 性も要求しない。
使われ方：全空間の表現を二端点と輸送 prism のデータへ移す主要比較。 -/
lemma intervalTransportCylinder_relativeFunctor_isQCatEquivalence {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) (d : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (relativeFunctorPre pointedSpaceProjection (p ≫ d)
      (pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁)) :=
  relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence pointedSpaceProjection _ _
    (intervalTransportCylinder_isPrecompositionEquivalence p f H h₀ h₁ hp)

end SerrePositivity.InfinityCategories
