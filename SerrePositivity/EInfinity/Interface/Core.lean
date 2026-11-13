module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.Homology
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
# E∞ 代数の準圏と忘却の中核

## 概要
HA §3.1・§3.2.2 に対応する E∞ 代数の準圏と D(S) への忘却を束ねる。

## 方針
離散代数の指定埋め込みと、指定された極限錐の像を記録する。

## 規約
基底環は Type u、準圏は SSet.{u+1} とする。

## 使われ方
BS 著者版 Proposition 8.5・Corollary 8.12 の CAlg 版から D(R) 版へ移す。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace SerrePositivity.EInfinity

attribute [local instance] HasDerivedCategory.standard

/-- 離散な可換 S 代数の圏。 -/
abbrev RingAlgebra (S : Type u) [CommRing S] := Under (CommRingCat.of S)

/-- 指定関手の頂点での値。 -/
abbrev atVertex {X Y : SSet.{u}} (F : X ⟶ Y) (x : X _⦋0⦌) : Y _⦋0⦌ :=
  F.app (Opposite.op ⦋0⦌) x

/-- HA §3.1・§3.2.2 のうち、指定極限と離散入力に用いる部分。 -/
structure EInfinityCore where
  CAlg (S : Type u) [CommRing S] : SSet.{u+1}
  quasicategory (S : Type u) [CommRing S] : Quasicategory (CAlg S)
  forget (S : Type u) [CommRing S] : CAlg S ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S
  forget_preservesLimits (S : Type u) [CommRing S]
      {K : SSet.{u+1}} {F : K ⟶ CAlg S} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (forget S) c)
  discrete (S : Type u) [CommRing S] : nerve (RingAlgebra S) ⟶ CAlg S
  discrete_forget (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (discrete S ≫ forget S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding S)
  discrete_recognition (S : Type u) [CommRing S] (x : (CAlg S) _⦋0⦌) :
    (∀ i : ℤ, i ≠ 0 → IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (atVertex (forget S) x))) ↔
    ∃ B : RingAlgebra S, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (atVertex (discrete S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)))

attribute [instance] EInfinityCore.quasicategory

end SerrePositivity.EInfinity
