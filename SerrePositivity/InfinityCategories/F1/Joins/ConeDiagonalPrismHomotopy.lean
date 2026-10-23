module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeDiagonalPrism

/-!
概要：元の native な Hom 比較の全円柱と、同じ三角形の対角を両端固定で結ぶ。
方針：最小値変形を元の正方形で評価する。
規約：元の Hom 比較・図式・指定始点を全時刻で保持する。
使われ方：三角形の長辺を元の標準比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 元の Hom 比較の円柱から同じ対角へ、全パラメータを保って変形する。 -/
def coneDiagonalPrismHomotopy (c : JoinCone f) (z : X _⦋0⦌) :
    SSet.Homotopy (coneParameterPrism (fixedApexConeHomComparison c z))
      (coneDiagonalPrism c z) where
  h := coneDiagonalDeformationParameters K (pinchedHom z c.vertex) ≫ conePointHomSquare c z
  h₀ := by
    rw [← Category.assoc, coneDiagonalDeformationParameters_zero, conePointHomSquare_source]
    rfl
  h₁ := by
    rw [← Category.assoc, coneDiagonalDeformationParameters_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 変形の始点側は全時刻で同じ指定始点。 -/
lemma coneDiagonalPrismHomotopy_left (c : JoinCone f) (z : X _⦋0⦌) :
    ((SSet.ι₀ (X := K) ▷ pinchedHom z c.vertex) ▷ (Δ[1] : SSet.{u})) ≫
      (coneDiagonalPrismHomotopy c z).h = SSet.const z := by
  change _ ≫ (coneDiagonalDeformationParameters K _ ≫ conePointHomSquare c z) = _
  rw [← Category.assoc, coneDiagonalDeformationParameters_left,
    Category.assoc, conePointHomSquare_source, Category.assoc,
    coneParameterPrism_zero, SSet.comp_const]

/-- 変形の図式側は全時刻で同じ元の図式。 -/
lemma coneDiagonalPrismHomotopy_right (c : JoinCone f) (z : X _⦋0⦌) :
    ((SSet.ι₁ (X := K) ▷ pinchedHom z c.vertex) ▷ (Δ[1] : SSet.{u})) ≫
      (coneDiagonalPrismHomotopy c z).h =
        fst (K ⊗ pinchedHom z c.vertex) Δ[1] ≫ fst K (pinchedHom z c.vertex) ≫ f := by
  change _ ≫ (coneDiagonalDeformationParameters K _ ≫ conePointHomSquare c z) = _
  rw [← Category.assoc, coneDiagonalDeformationParameters_right,
    Category.assoc, conePointHomSquare_one]
  rfl

end SerrePositivity.InfinityCategories
