module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitTriangleConeFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativeHomotopyRestriction
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryInverseRelative
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyRetargetValue
/-! # 単位三角形の相対比較から対角閉路の四辺固定を得る

概要：退化単位三角形への相対比較を、実対角閉路の二次元比較として保持する。
方針：同じ対角 cone へ前合成し、三つの固定面から正方形の四辺固定を回収する。
規約：供給待ちの相対比較を明示入力とし、閉路や全時間を変更しない。
使われ方：左単位面を消去する際の、関手圏の辺の類の零性を供給する。
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
lemma dgGluingInitialUnitConeFamily_degenerate_evaluate (b : K ⟶ intervalMappingSpace x y) :
    dgGluingInitialUnitConeFamily K ≫ (stdSimplex.σ (0 : Fin 2) ▷ K) ≫
        intervalMappingUncurry b = intervalMappingUncurry (functorHomotopyRefl b).h := by
  rw [← Category.assoc, dgGluingInitialUnitConeFamily_collapse,
    ← intervalMappingUncurry_precomp]
  rfl

variable (b : K ⟶ intervalMappingSpace x y) (l : SSet.Homotopy b b)
  (A : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
  (H : SSet.Homotopy A ((stdSimplex.σ (0 : Fin 2) ▷ K) ≫ intervalMappingUncurry b))
  (ha : dgGluingInitialUnitConeFamily K ≫ A = intervalMappingUncurry l.h)
  (hfaces : ∀ i : Fin 3, ((stdSimplex.δ i ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Δ[1] ⊗ K) Δ[1] ≫ (stdSimplex.δ i ▷ K) ≫
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ intervalMappingUncurry b)

def dgGluingUnitTriangleLoopUncurriedHomotopy :
    SSet.Homotopy (intervalMappingUncurry l.h)
      (intervalMappingUncurry (functorHomotopyRefl b).h) :=
  stableHomotopyRetarget (functorHomotopyPrecomp H (dgGluingInitialUnitConeFamily K)) ha
    (dgGluingInitialUnitConeFamily_degenerate_evaluate b)

lemma dgGluingUnitTriangleLoopUncurriedHomotopy_h :
    (dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha).h =
      (dgGluingInitialUnitConeFamily K ▷ (Δ[1] : SSet.{u})) ≫ H.h := rfl

include hfaces in
lemma dgGluingUnitTriangleLoopUncurriedHomotopy_source :
    (prismEndpoint 0 (K ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
        (dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha).h = SSet.const x := by
  have he := dgGluingRelativeHomotopy_restrict_fixed H
    (stdSimplex.δ (2 : Fin 3) ▷ K) (hfaces 2)
    (dgGluingInitialUnitConeFamily K) (prismEndpoint 0 (K ⊗ Δ[1]))
    (β_ K (Δ[1] : SSet.{u})).hom (dgGluingInitialUnitConeFamily_source K)
  rw [dgGluingUnitTriangleLoopUncurriedHomotopy_h]
  calc
    _ = fst (K ⊗ Δ[1]) (Δ[1] : SSet.{u}) ≫ prismEndpoint 0 (K ⊗ Δ[1]) ≫
        dgGluingInitialUnitConeFamily K ≫ (stdSimplex.σ (0 : Fin 2) ▷ K) ≫
          intervalMappingUncurry b := he
    _ = _ := by
      rw [dgGluingInitialUnitConeFamily_degenerate_evaluate b,
        intervalMappingUncurry_zero, SSet.comp_const]

include hfaces in
lemma dgGluingUnitTriangleLoopUncurriedHomotopy_target :
    (prismEndpoint 1 (K ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
        (dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha).h = SSet.const y := by
  have he := dgGluingRelativeHomotopy_restrict_fixed H
    (stdSimplex.δ (0 : Fin 3) ▷ K) (hfaces 0)
    (dgGluingInitialUnitConeFamily K) (prismEndpoint 1 (K ⊗ Δ[1]))
    (fst K (Δ[1] : SSet.{u}) ≫ prismEndpoint 1 K)
    (by simpa only [Category.assoc] using dgGluingInitialUnitConeFamily_target K)
  rw [dgGluingUnitTriangleLoopUncurriedHomotopy_h]
  calc
    _ = fst (K ⊗ Δ[1]) (Δ[1] : SSet.{u}) ≫ prismEndpoint 1 (K ⊗ Δ[1]) ≫
        dgGluingInitialUnitConeFamily K ≫ (stdSimplex.σ (0 : Fin 2) ▷ K) ≫
          intervalMappingUncurry b := he
    _ = _ := by
      rw [dgGluingInitialUnitConeFamily_degenerate_evaluate b,
        intervalMappingUncurry_one, SSet.comp_const]

include hfaces in
lemma dgGluingUnitTriangleLoopUncurriedHomotopy_zero_fixed :
    (((Δ[1] : SSet.{u}) ◁ (ι₀ : K ⟶ _)) ▷ Δ[1]) ≫
        (dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha).h =
      fst (Δ[1] ⊗ K) Δ[1] ≫ (Δ[1] ◁ (ι₀ : K ⟶ _)) ≫
        intervalMappingUncurry (functorHomotopyRefl b).h := by
  have he := dgGluingRelativeHomotopy_restrict_fixed H
    (stdSimplex.δ (1 : Fin 3) ▷ K) (hfaces 1)
    (dgGluingInitialUnitConeFamily K) ((Δ[1] : SSet.{u}) ◁ (ι₀ : K ⟶ _))
    (𝟙 (Δ[1] ⊗ K))
    (by simpa only [Category.id_comp] using dgGluingInitialUnitConeFamily_zero K)
  rw [dgGluingUnitTriangleLoopUncurriedHomotopy_h]
  simpa only [functorHomotopyPrecomp, Category.assoc,
    dgGluingInitialUnitConeFamily_degenerate_evaluate b] using he

include hfaces in
lemma dgGluingUnitTriangleLoopUncurriedHomotopy_one_fixed :
    (((Δ[1] : SSet.{u}) ◁ (ι₁ : K ⟶ _)) ▷ Δ[1]) ≫
        (dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha).h =
      fst (Δ[1] ⊗ K) Δ[1] ≫ (Δ[1] ◁ (ι₁ : K ⟶ _)) ≫
        intervalMappingUncurry (functorHomotopyRefl b).h := by
  have he := dgGluingRelativeHomotopy_restrict_fixed H
    (stdSimplex.δ (0 : Fin 3) ▷ K) (hfaces 0)
    (dgGluingInitialUnitConeFamily K) ((Δ[1] : SSet.{u}) ◁ (ι₁ : K ⟶ _))
    (𝟙 (Δ[1] ⊗ K))
    (by simpa only [Category.id_comp] using dgGluingInitialUnitConeFamily_one K)
  rw [dgGluingUnitTriangleLoopUncurriedHomotopy_h]
  simpa only [functorHomotopyPrecomp, Category.assoc,
    dgGluingInitialUnitConeFamily_degenerate_evaluate b] using he
end SerrePositivity.InfinityCategories
