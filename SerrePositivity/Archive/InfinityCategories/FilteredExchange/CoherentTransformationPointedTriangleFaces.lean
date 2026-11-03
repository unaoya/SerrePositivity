module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointedTriangle

/-!
概要：各 fiber の全 pointed 三角形の二辺を元の二つの普遍 prism と照合する。
方針：全三角形の二つの面の制限式を同じ fiber 包含で前合成する。
規約：全円柱の厳密な等式。使われ方：各点の元の二次整合と全空間作用の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}}
  (F G J : B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "a" => vertexFiber (leftUnstraighteningProjection F) b
local notation "s" => lift (vertexFiberι (leftUnstraighteningProjection F) b)
  (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "L" => coherentTransformationTriangleLift F G J x y T

/-- 概要：各 fiber の全三角形の第一辺は元の第一作用の指定 prism の制限。
方針：元の全持ち上げの第一面を制限。
規約：全円柱の等式。使われ方：元の第一脚の作用の照合。 -/
lemma coherentTransformationPointedTriangle_first :
    (stdSimplex.δ (2 : Fin 3) ▷ a) ≫ coherentTransformationPointedTriangle F G J x y T b =
      (Δ[1] ◁ s) ≫
        (unstraighteningMappingFamilyWitness F G
          (SSet.const x)).toRepresentationWitness.leftPrism := by
  calc
    _ = (Δ[1] ◁ s) ≫
        ((stdSimplex.δ (2 : Fin 3) ▷ (leftUnstraightening F ⊗ Δ[0])) ≫ (L).prism) := rfl
    _ = _ := congrArg
      (fun k : (Δ[1] : SSet.{u + 1}) ⊗ (leftUnstraightening F ⊗ Δ[0]) ⟶
        PointedSpaceInfinity.{u} => (Δ[1] ◁ s) ≫ k) (L).first

/-- 概要：各 fiber の第二辺は元の第一作用で引き戻した第二作用の指定 prism。
方針：元の全持ち上げの第二面を制限。
規約：元の二作用と全円柱を保持。使われ方：元の合成作用の照合。 -/
lemma coherentTransformationPointedTriangle_second :
    (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ coherentTransformationPointedTriangle F G J x y T b =
      (Δ[1] ◁ s) ≫
        (Δ[1] ◁ lift (relativeFunctorUncurry
          (SSet.const x ≫ leftUnstraighteningMappingSpaceMap F G))
          (snd (leftUnstraightening F) Δ[0])) ≫
            (unstraighteningMappingFamilyWitness G J
              (SSet.const y)).toRepresentationWitness.leftPrism := by
  calc
    _ = (Δ[1] ◁ s) ≫
        ((stdSimplex.δ (0 : Fin 3) ▷ (leftUnstraightening F ⊗ Δ[0])) ≫ (L).prism) := rfl
    _ = _ := congrArg
      (fun k : (Δ[1] : SSet.{u + 1}) ⊗ (leftUnstraightening F ⊗ Δ[0]) ⟶
        PointedSpaceInfinity.{u} => (Δ[1] ◁ s) ≫ k) (L).second

end SerrePositivity.InfinityCategories.F2
