module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCospanMap
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyExactComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
/-!
概要：厳密 cospan 比較は、完全な基底関手の下で選択 cofiber 差と全関手同型で可換する。
方針：指定全矢印族の厳密な回収式に、cofiber の制限・完全自然性を合成する。
規約：頂点別比較ではなく全パラメータの関手同型。使われ方：元 corner cone の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {A B C A' B' C' : SSet.{u}}
  [Quasicategory C] [Quasicategory C'] [IsStable C] [IsStable C']
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') [IsExactFunctor c]
  (hp : p ≫ c = a ≫ p') (hq : q ≫ c = b ≫ q')

def laxCospanCofiberComparison : FunctorIso
    (F2.laxPullbackCospanMap p q p' q' a b c hp hq ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber C' (F2.laxPullbackArrow p' q'))
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber C (F2.laxPullbackArrow p q) ≫ c) := by
  have h₁ := CofiberFamily.precompositionIso (F2.laxPullbackArrow p' q')
    (F2.laxPullbackCospanMap p q p' q' a b c hp hq)
  rw [F2.laxPullbackCospanMap_arrow] at h₁
  exact h₁.trans (CofiberFamily.familyExactComparison c (F2.laxPullbackArrow p q)).symm

end SerrePositivity.InfinityCategories
