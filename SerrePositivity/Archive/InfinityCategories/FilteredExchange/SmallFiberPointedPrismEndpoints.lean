module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberPointedPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberTriangleMiddle

/-!
概要：元の小さい fiber の普遍 prism の両端を、恒等な始点族と実際の fiber 作用へ同定する。
方針：元の証拠の両端条件と、一点評価・縮小の自然性を同じ全パラメータで適用する。
規約：元の全円柱を保持。使われ方：実際の fiber 射を表す切断族の端点の厳密な一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の普遍 prism を左表示の始点で評価すると、同じ pointed 始点族を回収する。 -/
lemma unstraighteningFamilyLeftPrism_source {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} {t : K ⟶ leftUnstraighteningTransformationSpace F G}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    (w : UnstraighteningFamilyWitness F G t f) :
    prismEndpoint 0 (leftUnstraightening F ⊗ K) ≫ w.leftPrism =
      fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F := by
  rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc]
  have h : prismEndpoint 0 (leftUnstraightening F ⊗ K) ≫
      (α_ Δ[1] (leftUnstraightening F) K).inv =
        prismEndpoint 0 (leftUnstraightening F) ▷ K := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [h, w.source]

variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌)
local notation "A" => leftUnstraightening F
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (Over.Hom.left m) (SSet.const l)
local notation "w" => unstraighteningMappingFamilyWitness F G (SSet.const x)

/-- 全 prism の始点は元の同じ fiber の pointed 始点族。 -/
lemma coherentSmallFiberPointedPrism_source :
    prismEndpoint 0 a ≫ coherentSmallFiberPointedPrism F G x b =
      coherentCospanFiberPointedSource F b := by
  unfold coherentSmallFiberPointedPrism
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
  change s ≫ prismEndpoint 0 (A ⊗ Δ[0]) ≫ (w).leftPrism = _
  rw [unstraighteningFamilyLeftPrism_source, ← Category.assoc, lift_fst]
  rfl

/-- 全 prism の終点は元の指定全空間作用の同じ fiber 上の制限。 -/
lemma coherentSmallFiberPointedPrism_target :
    prismEndpoint 1 a ≫ coherentSmallFiberPointedPrism F G x b =
      (m).left ≫ (leftUnstraighteningMappingVertexMap F G x).val ≫
        pullback.fst pointedSpaceProjection G := by
  unfold coherentSmallFiberPointedPrism
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
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

/-- 同じ全 prism の終点は、元の実際の小さい fiber 射を pointed 始点族へ写したもの。 -/
lemma coherentSmallFiberPointedPrism_target_fiber :
    prismEndpoint 1 a ≫ coherentSmallFiberPointedPrism F G x b =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) ≫
        coherentCospanFiberPointedSource G b :=
  (coherentSmallFiberPointedPrism_target F G x b).trans
    (coherentFiberPointedSource_naturality F G x b).symm

end SerrePositivity.InfinityCategories.F2
