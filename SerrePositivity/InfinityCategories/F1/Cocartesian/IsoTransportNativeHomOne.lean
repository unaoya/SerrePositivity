module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomZero

/-!
概要：全局所比較の一評価は、元の全 Hom の結合共役に続く同じ分類作用。
方針：結合共役の豊穣作用を、元の coherent 区間族の自然性へ渡す。
規約：元の全局所 Hom と既存の結合 span を保持する。
使われ方：元の結合同型による Hom 輸送との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ指定結合同型による、元の全局所 Hom の core の共役作用。 -/
def cocartesianIsoTransportNativeHomMap :
    SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ⟶
    SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q) :=
  (quasicategoryCoreEnrichedFunctor
    (isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))).map
    (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k p)
    (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k q)

/-- 同じ結合 span の一評価は、元の全局所 Hom の共役に続く分類作用そのもの。 -/
lemma cocartesianIsoTransportNativeHomComparison_one :
    cocartesianIsoTransportNativeHomComparison l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanOne l k p q =
    (SSet.uliftFunctor.{u + 1, u}).map (cocartesianIsoTransportNativeHomMap l k p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q) := by
  let X : CocartesianIsoTransportCategory A := cocartesianBaseChangeIsoTransportObject l k p
  let Y : CocartesianIsoTransportCategory A := cocartesianBaseChangeIsoTransportObject l k q
  let R : EnrichedFunctor SSet.{u} (CocartesianIsoTransportCategory A)
      (CocartesianFibrationCategory (nerve A)) :=
    quasicategoryCoreEnrichedFunctor
      (isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))
  have h := coherentHomIntervalComparison_uncurry_enriched_naturality R X Y
  apply intervalMappingUncurry_injective
  rw [cocartesianIsoTransportNativeHomComparison_one_uncurry, intervalMappingUncurry_precomp,
    cocartesianStraighteningHomInterval_uncurry]
  have hh := congrArg (fun f ↦ f ≫ cocartesianStraighteningCoherentMap A) h
  simp only [coherentHomIntervalComparison, pinchedHomToIntervalMappingSpace_uncurry,
    Category.assoc] at hh ⊢
  exact hh

end SerrePositivity.InfinityCategories
