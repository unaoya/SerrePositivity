module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanPointedConeLift
public import SerrePositivity.InfinityCategories.F2.NativePointedConeTriangleLift

/-!
概要：元の全 pointed fiber 三角形と全錐の持ち上げの始点族を厳密に揃える。
方針：元の第一辺の普遍 prism の始点条件を同じ fiber 上へ制限する。
規約：全パラメータを保持。使われ方：始点固定の可縮な延長空間での二三角形比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "s" => lift (Over.Hom.left m)
  (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "w" => unstraighteningMappingFamilyWitness F G (SSet.const x)

/-- 元の全三角形の最初の頂点は、全錐の持ち上げに使う同じ元の始点族。 -/
lemma coherentSmallFiberPointedTriangle_initial :
    (scaffoldFirstVertex 2 ▷ a) ≫ coherentSmallFiberPointedTriangle F G J x y T b =
      snd Δ[0] a ≫ coherentCospanFiberPointedSource F b := by
  have hz : (scaffoldFirstVertex 2 : (Δ[0] : SSet.{u + 1}) ⟶ Δ[2]) =
      scaffoldFirstVertex 1 ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [hz, comp_whiskerRight, Category.assoc, coherentSmallFiberPointedTriangle_first]
  have hs : (scaffoldFirstVertex 1 ▷ a) ≫ (Δ[1] ◁ s) ≫
      (α_ Δ[1] (leftUnstraightening F) Δ[0]).inv =
        (snd Δ[0] a ≫ s) ≫ (prismEndpoint 0 (leftUnstraightening F) ▷ Δ[0]) := by
    apply SSet.hom_ext
    intro n
    rfl
  change (scaffoldFirstVertex 1 ▷ a) ≫ (Δ[1] ◁ s) ≫
    (α_ Δ[1] (leftUnstraightening F) Δ[0]).inv ≫ (w).prism = _
  have hh := congrArg (fun q => q ≫ (w).prism) hs
  have ht : s ≫ fst (leftUnstraightening F) Δ[0] ≫
      pullback.fst pointedSpaceProjection F = coherentCospanFiberPointedSource F b := by
    rw [← Category.assoc, lift_fst]
    rfl
  simpa only [Category.assoc, (w).source, ht] using hh

end SerrePositivity.InfinityCategories.F2
