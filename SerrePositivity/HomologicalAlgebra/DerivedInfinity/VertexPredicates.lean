module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.Homology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 導来 ∞ 圏の頂点の連結性と p 完備性

コホモロジー次数の上界と、通常の導来圏へ移した主元完備性を定義する。
BS 著者版 Lemma 10.5・§8 の完備な代数の底の加群に用いる一般の述語。
複体や加群を変更する関手は構成せず、既存の導来同値で性質を読むだけである。
-/

@[expose] public noncomputable section
universe u
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
namespace SerrePositivity.DerivedInfinity

/-- コホモロジー次数が n 以下である頂点。
i>n の全ホモロジー加群が零であることを表す。BS 著者版 Lemma 10.5 の連結性はn=0。
底の加群の Subsingleton を使うので、既存の述語の型を保つ。 -/
def IsConnectiveAt (R : Type u) [CommRing R] (n : ℤ)
    (X : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : Prop :=
  ∀ i : ℤ, n < i → Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R i X)

/-- 導来 ∞ 圏の頂点が主元 p に関して導来完備であること。
既存の導来同値で通常の導来圏へ送り、IsCompleteを適用する。
BS 著者版 Definition 8.2 の底の加群の完備性などに用い、素数性は定義に不要。 -/
def IsPComplete (p : ℕ) (R : Type u) [CommRing R]
    (M : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : Prop :=
  DerivedCompletion.IsComplete R (p : R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩)

end SerrePositivity.DerivedInfinity

namespace SerrePositivity.InfinityCategories.Derived
/-- 旧名への互換の略記。実定義は一般の DerivedInfinity.IsConnectiveAt に一元化する。
既存の利用側の型を保ち、draftでの二重定義を不要にする。 -/
abbrev IsConnectiveAt (R : Type u) [CommRing R] (n : ℤ)
    (X : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : Prop :=
  SerrePositivity.DerivedInfinity.IsConnectiveAt R n X
end SerrePositivity.InfinityCategories.Derived

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived
/-- 旧名への互換の略記。実定義は一般の DerivedInfinity.IsPComplete にある。
BS固有の構成や証明には依存せず、既存の利用側の型だけを保つ。 -/
abbrev isPCompleteVertex (p : ℕ) (R : Type u) [CommRing R]
    (M : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : Prop :=
  SerrePositivity.DerivedInfinity.IsPComplete p R M
end SerrePositivity.BhattScholze.Perfectoidization.Derived
