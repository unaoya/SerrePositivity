module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison

/-!
# 同じ余単体的分解と Tot 増大の自然性

## 概要
元の余単体的入力の射を、同じ分解と二つの Tot 増大へ通す。

## 方針
既存の分解関手の増大の自然性を、交代余面と指定積 Tot へ施す。

## 規約
行の射は元の入力の射に分解関手を適用した実際の射である。

## 使われ方
BS 著者版 Lemma 4.22 の標準の完備導来比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
open HTComparisonResolution
variable {R : Type u} [CommRing R]

/-- 元の入力の射を、同じ余単体的分解へ施す。 -/
def resolvedCosimplicialMap {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    resolvedCosimplicial X ⟶ resolvedCosimplicial Y :=
  Functor.whiskerRight g (complexResolutionFunctor R)

/-- 同じ分解の増大は、元の入力の射について自然である。 -/
@[reassoc] theorem resolvedCosimplicialAugmentation_naturality
    {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    resolvedCosimplicialMap g ≫ resolvedCosimplicialAugmentation Y =
      resolvedCosimplicialAugmentation X ≫ g := by
  apply NatTrans.ext
  funext j
  exact (complexResolutionAugmentation R).naturality (g.app j)

/-- 元の指定積 Tot へ施す入力の射。 -/
abbrev cosimplicialTotalMap {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    cosimplicialTotal X ⟶ cosimplicialTotal Y :=
  (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
    ((alternatingCofaceMapComplex (Complex R)).map g)

/-- 分解した行の同じ指定積 Tot へ施す射。 -/
abbrev resolvedCosimplicialTotalMap {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    cosimplicialTotal (resolvedCosimplicial X) ⟶ cosimplicialTotal (resolvedCosimplicial Y) :=
  cosimplicialTotalMap (resolvedCosimplicialMap g)

/-- 同じ Tot 増大は元の入力の射と可換である。 -/
@[reassoc] theorem resolvedCosimplicialTotalAugmentation_naturality
    {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    resolvedCosimplicialTotalMap g ≫ resolvedCosimplicialTotalAugmentation Y =
      resolvedCosimplicialTotalAugmentation X ≫ cosimplicialTotalMap g := by
  have h := congrArg (fun k => (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
    ((alternatingCofaceMapComplex (Complex R)).map k)) (resolvedCosimplicialAugmentation_naturality g)
  simpa only [Functor.map_comp, resolvedCosimplicialTotalMap, cosimplicialTotalMap,
    resolvedCosimplicialTotalAugmentation, cosimplicialTotal, total] using h

/-- Tot を解消した同じ源の模型へ施す射。 -/
abbrev resolvedTotalModelMap {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    (complexResolutionFunctor R).obj (cosimplicialTotal (resolvedCosimplicial X)) ⟶
      (complexResolutionFunctor R).obj (cosimplicialTotal (resolvedCosimplicial Y)) :=
  (complexResolutionFunctor R).map (resolvedCosimplicialTotalMap g)

/-- 二つの指定増大の合成も、元の入力の射と可換である。 -/
@[reassoc] theorem resolvedTotalModelAugmentation_naturality
    {X Y : CosimplicialObject (Complex R)} (g : X ⟶ Y) :
    resolvedTotalModelAugmentation X ≫ cosimplicialTotalMap g =
      resolvedTotalModelMap g ≫ resolvedTotalModelAugmentation Y := by
  dsimp only [resolvedTotalModelAugmentation]
  rw [Category.assoc, ← resolvedCosimplicialTotalAugmentation_naturality]
  have hπ := (complexResolutionAugmentation R).naturality (resolvedCosimplicialTotalMap g)
  simp only [Functor.id_map] at hπ
  rw [← Category.assoc, ← hπ]
  exact Category.assoc _ _ _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
