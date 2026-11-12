module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.HomotopyTriangleEdges

/-!
概要：指定円柱を退化三角形へ入れ、定値辺と元の辺を厳密に回収する。
方針：二つの退化写像の三辺を計算する。
規約：元の全円柱を保持する。
使われ方：指定部分上で片側が定値な相対比較円柱の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K X : SSet.{u}} {f g : K ⟶ X} (H : SSet.Homotopy f g)

/-- 概要：元の指定円柱を退化三角形に入れる。
方針：時間を左へ移して退化写像を前合成。規約：e は潰す辺。使われ方：相対合成の境界。 -/
def degenerateHomotopyTriangle (e : Fin 2) : (Δ[2] : SSet.{u}) ⊗ K ⟶ X :=
  (stdSimplex.σ e ▷ K) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h

/-- 概要：σ₀ の第一辺は始点で定値。
方針：退化面と端点の式。規約：全円柱。使われ方：定値な第一境界円柱の指定。 -/
lemma degenerateHomotopyTriangle_zero_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ degenerateHomotopyTriangle H 0 =
      snd (Δ[1] : SSet.{u}) K ≫ f := by
  rw [degenerateHomotopyTriangle, ← comp_whiskerRight_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangle_degenerate_zero_first, comp_whiskerRight, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalVertex_zero_tensor]
  change snd (Δ[1] : SSet.{u}) K ≫ SSet.ι₀ ≫ H.h = _
  rw [H.h₀]

/-- 概要：σ₀ の第二辺は元の指定円柱。
方針：退化面の式。規約：厳密な回収。使われ方：指定第二境界円柱の保持。 -/
lemma degenerateHomotopyTriangle_zero_last :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ degenerateHomotopyTriangle H 0 =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
  rw [degenerateHomotopyTriangle, ← comp_whiskerRight_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangle_degenerate_zero_last, id_whiskerRight, Category.id_comp]

/-- 概要：σ₀ の長辺も元の指定円柱。
方針：退化面の式。規約：厳密な回収。使われ方：合成後の指定境界円柱。 -/
lemma degenerateHomotopyTriangle_zero_long :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ degenerateHomotopyTriangle H 0 =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
  rw [degenerateHomotopyTriangle, ← comp_whiskerRight_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.homotopyTriangle_degenerate_zero_long, id_whiskerRight, Category.id_comp]

/-- 概要：σ₁ の第一辺は元の指定円柱。
方針：退化面の式。規約：厳密な回収。使われ方：指定第一境界円柱の保持。 -/
lemma degenerateHomotopyTriangle_one_first :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ degenerateHomotopyTriangle H 1 =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
  have h : stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective; decide
  rw [degenerateHomotopyTriangle, ← comp_whiskerRight_assoc, h, id_whiskerRight, Category.id_comp]

/-- 概要：σ₁ の第二辺は終点で定値。
方針：退化面と端点の式。規約：全円柱。使われ方：定値な第二境界円柱の指定。 -/
lemma degenerateHomotopyTriangle_one_last :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ degenerateHomotopyTriangle H 1 =
      snd (Δ[1] : SSet.{u}) K ≫ g := by
  have h : stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) =
      (stdSimplex.σ (0 : Fin 1) : (Δ[1] : SSet.{u}) ⟶ Δ[0]) ≫
        stdSimplex.δ (0 : Fin 2) := by
    apply SSet.yonedaEquiv.injective; decide
  rw [degenerateHomotopyTriangle, ← comp_whiskerRight_assoc, h, comp_whiskerRight,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalVertex_one_tensor]
  change snd (Δ[1] : SSet.{u}) K ≫ SSet.ι₁ ≫ H.h = _
  rw [H.h₁]

/-- 概要：σ₁ の長辺も元の指定円柱。
方針：退化面の式。規約：厳密な回収。使われ方：合成後の指定境界円柱。 -/
lemma degenerateHomotopyTriangle_one_long :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ degenerateHomotopyTriangle H 1 =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
  have h : stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective; decide
  rw [degenerateHomotopyTriangle, ← comp_whiskerRight_assoc, h, id_whiskerRight, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
