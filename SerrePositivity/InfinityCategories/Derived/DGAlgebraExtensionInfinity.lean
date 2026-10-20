module
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraDerivedInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedFunctor
/-!
概要：非可換 dg 代数の射に沿う相対 tensor の実 ∞ 関手。
方針：モノイド対象の同じ単位・積保存から一対象 dg 関手を作り、graph 延長を使う。
規約：元の dg 代数の基礎環上の平坦性を要求しない。使われ方：β5 の ⊗_A B。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
/-- 単位・積を保つ dg 代数の射は、同じ Hom 鎖写像の一対象 dg 関手を与える。 -/
def dgAlgebraPointMap (f : B ⟶ C) : DGFunctor R (DGAlgebraPoint R B) (DGAlgebraPoint R C) where
  obj _ := .star
  map _ _ := f.hom
  map_id _ := IsMonHom.one_hom f.hom
  map_comp _ _ _ := IsMonHom.mul_hom f.hom
/-- 右加群の向きに揃えた、dg 代数の射の実一対象 dg 関手。 -/
def dgAlgebraMap (f : B ⟶ C) : DGFunctor R (dgAlgebraCategory R B) (dgAlgebraCategory R C) :=
  (dgAlgebraPointMap R f).op
/-- 非可換 dg 代数の射 B→C に沿う、−⊗ᴸ_B C の実 ∞ 関手。 -/
def dgAlgebraExtensionInfinity (f : B ⟶ C) :
    dgAlgebraDerivedInfinityCategory R B ⟶ dgAlgebraDerivedInfinityCategory R C :=
  dgModuleExtensionInfinity R _ _ (dgAlgebraMap R f)
/-- 非可換 dg 代数の射に沿う相対 tensor の実 ∞ 関手は完全。 -/
theorem dgAlgebraExtensionInfinity_isExactFunctor (f : B ⟶ C) :
    IsExactFunctor (dgAlgebraExtensionInfinity R f) :=
  dgModuleExtensionInfinity_isExactFunctor R _ _ (dgAlgebraMap R f)
end SerrePositivity.InfinityCategories
