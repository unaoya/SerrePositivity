module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DerivedComparisonShift
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.MappingExt

/-! # 標準導来圏での semifree 比較の具体化

概要：導来圏の標準 instance で任意の可換環と整数環の同値を検査する。
方針：公開同値を直接適用し、逆関手・単位・余単位も型検査する。
規約：`HasDerivedCategory.standard` はこのファイル内だけで有効にする。
使われ方：任意の導来圏の選択に依存しない具体化の回帰検査。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
attribute [local instance] HasDerivedCategory.standard

example (S : Type u) [CommRing S] :
    DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) ≌ DerivedCategory (ModuleCat.{u} S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S

example : DifferentialGraded.HomotopyCategory ℤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree ℤ) ≌
    DerivedCategory (ModuleCat.{0} ℤ) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence ℤ

example (S : Type u) [CommRing S] :
    DerivedCategory (ModuleCat.{u} S) ⥤ DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).inverse

example (S : Type u) [CommRing S] :
    𝟭 _ ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).functor ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).inverse :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).unitIso

example (S : Type u) [CommRing S] :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).inverse ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).functor ≅ 𝟭 _ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).counitIso

example (S : Type u) [CommRing S] :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).functor.CommShift ℤ := inferInstance

example : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence ℤ).functor.CommShift ℤ := inferInstance

example {I : Type u} (P : I → Complex ℤ)
    (hP : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree ℤ (P i)) [Small.{0} I] :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree ℤ (Limits.sigmaObj P) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_coproduct ℤ P hP

example (S : Type u) [CommRing S] :
    SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)) ≌
      DerivedCategory (ModuleCat.{u} S) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S

example : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory ℤ ≌ DerivedCategory (ModuleCat.{0} ℤ) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence ℤ

example (S : Type u) [CommRing S] :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.CommShift ℤ := inferInstance

example : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence ℤ).functor.CommShift ℤ := inferInstance

open scoped _root_.Simplicial

example (S : Type u) [CommRing S] (x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) (n : ℕ) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (x.obj 0) (y.obj 0)) n
      (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.pinchedHomZeroVertex (x.obj 0) (y.obj 0)) ≃*
        Multiplicative (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityExt x y (-((n + 1 : ℕ) : ℤ)))) :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityPiExtEquiv x y n⟩

example (S : Type u) [CommRing S] (x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    Nonempty (SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (x.obj 0) (y.obj 0)) ≃
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityExt x y 0) := ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityPiZeroExtEquiv x y⟩

end SerrePositivity.InfinityCategories
