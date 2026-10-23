module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberTriangleFaces
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeUncurryPointVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFiberPointedSourceNaturality

/-!
概要：元の全 pointed 三角形の中間頂点は、元の第一作用の実際の fiber 射である。
方針：指定第一辺の prism の終点条件、一点評価、縮小の自然性を順に適用する。
規約：元の全三角形・全 fiber を保持。使われ方：native 切断族の二脚の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 左表示の元の普遍 prism を終点で評価すると同じ作用射を回収する。 -/
lemma unstraighteningFamilyLeftPrism_target {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} {t : K ⟶ leftUnstraighteningTransformationSpace F G}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    (w : UnstraighteningFamilyWitness F G t f) :
    prismEndpoint 1 (leftUnstraightening F ⊗ K) ≫ w.leftPrism =
      f ≫ pullback.fst pointedSpaceProjection G := by
  rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc]
  have h : prismEndpoint 1 (leftUnstraightening F ⊗ K) ≫
      (α_ Δ[1] (leftUnstraightening F) K).inv =
        prismEndpoint 1 (leftUnstraightening F) ▷ K := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [h, w.target]

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
local notation "w" => unstraighteningMappingFamilyWitness F G (SSet.const x)
local notation "H" => coherentSmallFiberPointedTriangle F G J x y T b

/-- 元の中間頂点の全族は元の第一変換の全空間作用の同じ制限である。 -/
lemma coherentSmallFiberPointedTriangle_middle :
    prismEndpoint 1 a ≫ (stdSimplex.δ (2 : Fin 3) ▷ a) ≫ H =
      (m).left ≫ (leftUnstraighteningMappingVertexMap F G x).val ≫
        pullback.fst pointedSpaceProjection G := by
  rw [coherentSmallFiberPointedTriangle_first, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc]
  change s ≫ prismEndpoint 1 (A ⊗ Δ[0]) ≫ (w).leftPrism = _
  rw [unstraighteningFamilyLeftPrism_target]
  have hs : s = (m).left ≫ lift (𝟙 A) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hs]
  simpa only [Category.assoc] using congrArg
    (fun k : A ⟶ leftUnstraightening G => (m).left ≫ k ≫ pullback.fst pointedSpaceProjection G)
    (unstraighteningUncurryConst_point F G x l)

/-- 元の中間頂点は、小さい実際の fiber 射を pointed 始点族へ写したもの。 -/
lemma coherentSmallFiberPointedTriangle_middle_fiber :
    prismEndpoint 1 a ≫ (stdSimplex.δ (2 : Fin 3) ▷ a) ≫ H =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) ≫
        coherentCospanFiberPointedSource G b :=
  (coherentSmallFiberPointedTriangle_middle F G J x y T b).trans
    (coherentFiberPointedSource_naturality F G x b).symm

end SerrePositivity.InfinityCategories.F2
