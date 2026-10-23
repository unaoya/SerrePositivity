module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberPointedPrismEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberTriangleFaces

/-!
概要：元の全三角形の二辺を、元の二 fiber 作用を表す同じ普遍 prism へ同定する。
方針：第一辺の式を再利用し、第二辺への代入を縮小・fiber 作用の自然性で照合する。
規約：全円柱の厳密な一致。使われ方：native 錐の比較を実際の fiber cospan の切断族へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pG" => smallLeftUnstraighteningProjection G
local notation "mf" => smallUnstraighteningSourceRestriction F (vertexFiberι pF b)
local notation "mg" => smallUnstraighteningSourceRestriction G (vertexFiberι pG b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "sf" => lift (Over.Hom.left mf) (SSet.const l)
local notation "sg" => lift (Over.Hom.left mg) (SSet.const l)
local notation "fx" => CategoryTheory.Functor.map SSet.uliftFunctor (vertexFiberMap pF pG
  (coherentTransformationTotalMap F G x) (coherentTransformationTotalMap_projection F G x) b)
local notation "f" => relativeFunctorUncurry (SSet.const x ≫ leftUnstraighteningMappingSpaceMap F G)

/-- 第一面は元の第一 fiber 作用の全 prism そのもの。 -/
lemma coherentSmallFiberPointedTriangle_first_prism :
    (stdSimplex.δ (2 : Fin 3) ▷ a) ≫ coherentSmallFiberPointedTriangle F G J x y T b =
      coherentSmallFiberPointedPrism F G x b :=
  coherentSmallFiberPointedTriangle_first F G J x y T b

/-- 元の定値変換を一点で作用させた始域族は、同じ小さい fiber 射で制限した始域族。 -/
lemma coherentSmallFiberPrism_parameter_naturality :
    sf ≫ lift f (snd (leftUnstraightening F) Δ[0]) = fx ≫ sg := by
  have hs : sf = (mf).left ≫ lift (𝟙 (leftUnstraightening F)) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    rfl
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, hs, Category.assoc, unstraighteningUncurryConst_point,
      Category.assoc, lift_fst]
    exact (coherentFiberSourceRestriction_naturality F G x b).symm
  · apply SSet.hom_ext
    intro n
    rfl

/-- 第二面は、元の第一 fiber 射で代入した同じ第二 fiber 作用の全 prism。 -/
lemma coherentSmallFiberPointedTriangle_second_prism :
    (stdSimplex.δ (0 : Fin 3) ▷ a) ≫ coherentSmallFiberPointedTriangle F G J x y T b =
      (Δ[1] ◁ fx) ≫ coherentSmallFiberPointedPrism G J y b := by
  rw [coherentSmallFiberPointedTriangle_second]
  unfold coherentSmallFiberPointedPrism
  change (Δ[1] ◁ sf) ≫ (Δ[1] ◁ lift f (snd (leftUnstraightening F) Δ[0])) ≫
    (unstraighteningMappingFamilyWitness G J (SSet.const y)).leftPrism =
      (Δ[1] ◁ fx) ≫ (Δ[1] ◁ sg) ≫
        (unstraighteningMappingFamilyWitness G J (SSet.const y)).leftPrism
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    coherentSmallFiberPrism_parameter_naturality F G x b,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2
