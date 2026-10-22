module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiberTransportTriangleFamily
public import SerrePositivity.InfinityCategories.F1.CoherentTransformationFamilyTriangle
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningParametrizedTransport

/-!
概要：元の coherent な三角形の全族を、同じ評価点での輸送族へ制限する。
方針：三角形の元の評価を取り、各辺を元の全変換の輸送族と厳密に同定する。
規約：元の辺の族と、元の全 fiber Hom 比較の写像を保持する。
使われ方：Yoneda 評価の前合成との両立を、全パラメータで証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の変換の族の共同評価を固定点へ制限すると、同じ区間族の評価そのもの。 -/
lemma coherentTransformationFamilyDiagram_evaluate {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (b : B _⦋0⦌) :
    (Δ[1] ◁ lift (SSet.const b) (𝟙 K)) ≫ coherentTransformationFamilyDiagram t =
      intervalMappingUncurry t ≫ evaluateFunctorAt b := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, k⟩
  rfl

/-- 元の三角形の全族を、同じ元の評価点へ制限する。 -/
def coherentTriangleEvaluate {B K : SSet.{u + 1}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u} :=
  (Δ[2] ◁ lift (SSet.const b) (𝟙 K)) ≫ H

/-- 同じ三角形の辺を評価すると、元の同じ変換の区間族の評価になる。 -/
lemma coherentTriangleEvaluate_edge {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (i : Fin 3) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (hi : (stdSimplex.δ i ▷ (B ⊗ K)) ≫ H = coherentTransformationFamilyDiagram t) :
    (stdSimplex.δ i ▷ K) ≫ coherentTriangleEvaluate H b =
      intervalMappingUncurry t ≫ evaluateFunctorAt b := by
  rw [coherentTriangleEvaluate, trianglePrism_restrict_baseChange, hi,
    coherentTransformationFamilyDiagram_evaluate]

/-- 元の三角形の指定辺の輸送族を、元の全変換の同じ持ち上げから取る。 -/
def coherentTriangleFiberTransportFamily {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (i : Fin 3) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (hi : (stdSimplex.δ i ▷ (B ⊗ K)) ≫ H = coherentTransformationFamilyDiagram t) :
    FiberTransportFamily (b := G.app _ b) pointedSpaceProjection
      (𝟙 (vertexFiber pointedSpaceProjection (F.app _ b)))
      ((stdSimplex.δ i ▷ K) ≫ coherentTriangleEvaluate H b) := by
  let U := (leftUnstraighteningFiberTransportFamily F G b).precomp t
  have he : (Δ[1] ◁ t) ≫
      (intervalMappingUncurry (𝟙 (leftUnstraighteningTransformationSpace F G)) ≫
        evaluateFunctorAt b) = (stdSimplex.δ i ▷ K) ≫ coherentTriangleEvaluate H b := by
    rw [← Category.assoc, ← intervalMappingUncurry_precomp, Category.comp_id]
    exact (coherentTriangleEvaluate_edge H b i t hi).symm
  exact ⟨U.endpoint, U.prism, U.start, U.finish, by rw [U.over_base, he]⟩

/-- 同じ指定辺の輸送族の写像は、元の全 fiber Hom 比較の同じパラメータ制限。 -/
lemma coherentTriangleFiberTransportFamily_map {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (i : Fin 3) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (hi : (stdSimplex.δ i ▷ (B ⊗ K)) ≫ H = coherentTransformationFamilyDiagram t) :
    (coherentTriangleFiberTransportFamily F G H b i t hi).map =
      t ≫ leftUnstraighteningMappingFiberHom F G b := by
  change ((leftUnstraighteningFiberTransportFamily F G b).precomp t).map = _
  rw [FiberTransportFamily.precomp_map, leftUnstraighteningFiberTransportFamily_map]

end SerrePositivity.InfinityCategories.HomotopyLimits
