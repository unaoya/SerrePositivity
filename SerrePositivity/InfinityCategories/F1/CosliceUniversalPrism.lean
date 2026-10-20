module

public import SerrePositivity.InfinityCategories.F1.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：coslice 全体の普遍錐を、固定始点から射影への一つの区間族として表す。
方針：左 join の円柱比較を普遍錐で評価し、制限と恒等錐での値を計算する。
規約：底の充填性を仮定しない。恒等錐上では区間全体が厳密に定値。
使われ方：Hom 関手の unstraightening への大域比較と、標準輸送の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- coslice の全対象を同時に扱う、固定始点から元の射影への標準区間族。 -/
def cosliceUniversalPrism {B : SSet.{u}} (b : B _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ sliceUnder (SSet.yonedaEquiv.symm b) ⟶ B :=
  leftMappingSpacePrism _ ≫ sliceUnderUncurry (𝟙 _)

/-- 普遍区間族の始点は、元の頂点に全次数で定値。 -/
lemma cosliceUniversalPrism_zero {B : SSet.{u}} (b : B _⦋0⦌) :
    prismEndpoint 0 _ ≫ cosliceUniversalPrism b = SSet.const b := by
  rw [cosliceUniversalPrism, ← Category.assoc, leftMappingSpacePrism_zero,
    Category.assoc, sliceUnderUncurry_fixed, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
/-- 普遍区間族の終点は、元の coslice 射影そのもの。 -/
lemma cosliceUniversalPrism_one {B : SSet.{u}} (b : B _⦋0⦌) :
    prismEndpoint 1 _ ≫ cosliceUniversalPrism b =
      sliceUnderProjection (SSet.yonedaEquiv.symm b) := by
  rw [cosliceUniversalPrism, ← Category.assoc, leftMappingSpacePrism_one,
    sliceUnderUncurry_projection, Category.id_comp]

/-- 任意のパラメーターへの制限は、元の錐の同じ標準左区間族を与える。 -/
lemma cosliceUniversalPrism_precomp {A B : SSet.{u}} (b : B _⦋0⦌)
    (f : A ⟶ sliceUnder (SSet.yonedaEquiv.symm b)) :
    (Δ[1] ◁ f) ≫ cosliceUniversalPrism b =
      leftMappingSpacePrism A ≫ sliceUnderUncurry f := by
  rw [cosliceUniversalPrism, ← Category.assoc, leftMappingSpacePrism_naturality,
    Category.assoc, ← sliceUnderUncurry_precomp, Category.comp_id]

/-- 恒等錐への制限では、標準区間全体が元の始点に厳密に定値となる。 -/
lemma cosliceUniversalPrism_identity {B : SSet.{u}} (b : B _⦋0⦌) :
    (Δ[1] ◁ SSet.yonedaEquiv.symm (cosliceIdentityCone b)) ≫
      cosliceUniversalPrism b = SSet.const b := by
  rw [cosliceUniversalPrism_precomp, sliceUnderUncurry_yoneda]
  exact SSet.comp_const _ _

end SerrePositivity.InfinityCategories
