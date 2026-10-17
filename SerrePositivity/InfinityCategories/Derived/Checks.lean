module
public import SerrePositivity.InfinityCategories.Derived.DerivedComparison

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
    DifferentialGraded.HomotopyCategory S (Semifree S) ≌ DerivedCategory (ModuleCat.{u} S) :=
  semifreeDerivedEquivalence S

example : DifferentialGraded.HomotopyCategory ℤ (Semifree ℤ) ≌
    DerivedCategory (ModuleCat.{0} ℤ) := semifreeDerivedEquivalence ℤ

example (S : Type u) [CommRing S] :
    DerivedCategory (ModuleCat.{u} S) ⥤ DifferentialGraded.HomotopyCategory S (Semifree S) :=
  (semifreeDerivedEquivalence S).inverse

example (S : Type u) [CommRing S] :
    𝟭 _ ≅ (semifreeDerivedEquivalence S).functor ⋙ (semifreeDerivedEquivalence S).inverse :=
  (semifreeDerivedEquivalence S).unitIso

example (S : Type u) [CommRing S] :
    (semifreeDerivedEquivalence S).inverse ⋙ (semifreeDerivedEquivalence S).functor ≅ 𝟭 _ :=
  (semifreeDerivedEquivalence S).counitIso

end SerrePositivity.InfinityCategories
