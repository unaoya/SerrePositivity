module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCollarDiagonalTriangleFamilies
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
/-! # 同じ四面体上の実補正対角を写像空間の三角形へ戻す

概要：四面体から取り出した二補正道を、写像空間の三角形の指定面として保持する。
方針：有限再添字の端点は二つの既知面へ退化するため、区間の端点固定から curry する。
規約：三角形全体の両端を固定し、二つの実補正道を変更しない。
使われ方：native 高次貼り合わせの対角合成三角形を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K Z : SSet.{u}} {x y : Z _⦋0⦌}
  (V : (Δ[1] : SSet.{u}) ⊗ (Δ[3] ⊗ K) ⟶ Z)
  (a b : K ⊗ Δ[1] ⟶ intervalMappingSpace x y)
  (ha : (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
      dgGluingUnitCollarDiagonalTriangleDomain K ≫ V =
    (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫ intervalMappingUncurry a)
  (hb : (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
      dgGluingUnitCollarDiagonalTriangleDomain K ≫ V =
    (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫ intervalMappingUncurry b)

include ha in
lemma dgGluingUnitCollarIntervalTriangle_source :
    prismEndpoint 0 (Δ[2] ⊗ K) ≫ dgGluingUnitCollarDiagonalTriangleDomain K ≫ V =
      SSet.const x := by
  rw [← Category.assoc, dgGluingUnitCollarDiagonalTriangleDomain_source_retract]
  simp only [Category.assoc]
  rw [ha]
  rw [← Category.assoc (prismEndpoint 0 (Δ[1] ⊗ K)) _, prismEndpoint_naturality]
  simp only [Category.assoc]
  rw [intervalMappingUncurry_zero, SSet.comp_const, SSet.comp_const]

include hb in
lemma dgGluingUnitCollarIntervalTriangle_target :
    prismEndpoint 1 (Δ[2] ⊗ K) ≫ dgGluingUnitCollarDiagonalTriangleDomain K ≫ V =
      SSet.const y := by
  rw [← Category.assoc, dgGluingUnitCollarDiagonalTriangleDomain_target_retract]
  simp only [Category.assoc]
  rw [hb]
  rw [← Category.assoc (prismEndpoint 1 (Δ[1] ⊗ K)) _, prismEndpoint_naturality]
  simp only [Category.assoc]
  rw [intervalMappingUncurry_one, SSet.comp_const, SSet.comp_const]

def dgGluingUnitCollarIntervalTriangle : Δ[2] ⊗ K ⟶ intervalMappingSpace x y :=
  intervalMappingCurryOfEndpoints (dgGluingUnitCollarDiagonalTriangleDomain K ≫ V)
    (dgGluingUnitCollarIntervalTriangle_source V a ha)
    (dgGluingUnitCollarIntervalTriangle_target V b hb)

lemma dgGluingUnitCollarIntervalTriangle_evaluate :
    intervalMappingUncurry (dgGluingUnitCollarIntervalTriangle V a b ha hb) =
      dgGluingUnitCollarDiagonalTriangleDomain K ≫ V :=
  intervalMappingUncurry_curryOfEndpoints _ _ _

lemma dgGluingUnitCollarIntervalTriangle_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingUnitCollarIntervalTriangle V a b ha hb =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ a := by
  apply intervalMappingUncurry_injective x y
  rw [intervalMappingUncurry_precomp, dgGluingUnitCollarIntervalTriangle_evaluate,
    intervalMappingUncurry_precomp]
  exact ha

lemma dgGluingUnitCollarIntervalTriangle_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingUnitCollarIntervalTriangle V a b ha hb =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ b := by
  apply intervalMappingUncurry_injective x y
  rw [intervalMappingUncurry_precomp, dgGluingUnitCollarIntervalTriangle_evaluate,
    intervalMappingUncurry_precomp]
  exact hb
end SerrePositivity.InfinityCategories
