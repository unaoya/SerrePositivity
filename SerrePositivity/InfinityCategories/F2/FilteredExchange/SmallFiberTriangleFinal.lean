module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberTriangleMiddle

/-!
概要：元の全 pointed 三角形の最後の頂点を、元の二つの実際の fiber 射の合成へ同定する。
方針：指定第二辺の prism の終点条件と、定値二変換の合成の一点評価を使う。
規約：元の二作用と全族を保持。使われ方：左右三角形の共通終点と指定 path の比較。
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
local notation "A" => leftUnstraightening F
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (Over.Hom.left m) (SSet.const l)
local notation "u₀" => relativeFunctorUncurry
  (SSet.const x ≫ leftUnstraighteningMappingSpaceMap F G)
local notation "u₁" => relativeFunctorUncurry
  (SSet.const y ≫ leftUnstraighteningMappingSpaceMap G J)
local notation "t" => lift u₀ (snd A Δ[0])
local notation "w" => unstraighteningMappingFamilyWitness G J (SSet.const y)
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b
local notation "fx" => vertexFiberMap (smallLeftUnstraighteningProjection F)
  (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
  (coherentTransformationTotalMap_projection F G x) b
local notation "fy" => vertexFiberMap (smallLeftUnstraighteningProjection G)
  (smallLeftUnstraighteningProjection J) (coherentTransformationTotalMap G J y)
  (coherentTransformationTotalMap_projection G J y) b

/-- 元の最終頂点は、同じ二つの縮小前の全空間作用の指定合成。 -/
lemma coherentSmallFiberPointedTriangle_final :
    prismEndpoint 1 a ≫ (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ H =
      (m).left ≫ (leftUnstraighteningMappingVertexMap F G x).val ≫
        (leftUnstraighteningMappingVertexMap G J y).val ≫
          pullback.fst pointedSpaceProjection J := by
  have hface : (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ H =
      (Δ[1] ◁ (s ≫ t)) ≫ (w).leftPrism := by
    rw [coherentSmallFiberPointedTriangle_second, ← Category.assoc, ← whiskerLeft_comp]
    rfl
  rw [hface, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    unstraighteningFamilyLeftPrism_target]
  have hs : s = (m).left ≫ lift (𝟙 A) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hs]
  simpa only [Category.assoc] using congrArg
    (fun k : A ⟶ leftUnstraightening J => (m).left ≫ k ≫ pullback.fst pointedSpaceProjection J)
    (unstraighteningUncurryConstComposite_point F G J x y l)

/-- 同じ最終頂点は、元の実際の小さい二つの fiber 射の合成の pointed 表示。 -/
lemma coherentSmallFiberPointedTriangle_final_fiber :
    prismEndpoint 1 a ≫ (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ H =
      (SSet.uliftFunctor.{u + 1, u}).map (fx ≫ fy) ≫ coherentCospanFiberPointedSource J b := by
  have hx := congrArg
    (fun k => k ≫ (leftUnstraighteningMappingVertexMap G J y).val ≫
      pullback.fst pointedSpaceProjection J)
    (coherentFiberSourceRestriction_naturality F G x b)
  have hy := congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map fx ≫ k)
    (coherentFiberPointedSource_naturality G J y b)
  have hxy := hy.trans (by simpa only [Category.assoc] using hx)
  exact (coherentSmallFiberPointedTriangle_final F G J x y T b).trans
    (by simpa only [Functor.map_comp, Category.assoc] using hxy.symm)

end SerrePositivity.InfinityCategories.F2
