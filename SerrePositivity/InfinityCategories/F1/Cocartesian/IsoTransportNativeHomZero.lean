module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomEndpoints
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalUncurryNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningHomInterval

/-!
概要：全局所比較の零評価は、元の二重引き戻し間の同じ分類 Hom 作用そのもの。
方針：始域評価の豊穣 Hom 作用が恒等であることを、coherent 区間族の自然性へ渡す。
規約：元の全局所 Hom と既存の結合 span を保持する。
使われ方：同じ結合 Hom 輸送と元の分類作用の比較。
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

/-- 始域評価の元の core Hom への作用は、全局所 Hom 上で恒等。 -/
lemma cocartesianIsoTransportSource_map_identity (X Y : CocartesianIsoTransportCategory A) :
    (quasicategoryCoreEnrichedFunctor
      (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))).map X Y =
    𝟙 (SimplicialCategory.sHom X Y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 同じ結合 span の零評価は、元の全局所 Hom の分類作用そのもの。 -/
lemma cocartesianIsoTransportNativeHomComparison_zero :
    cocartesianIsoTransportNativeHomComparison l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanZero l k p q =
    cocartesianStraighteningHomInterval
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := by
  let X : CocartesianIsoTransportCategory A := cocartesianBaseChangeIsoTransportObject l k p
  let Y : CocartesianIsoTransportCategory A := cocartesianBaseChangeIsoTransportObject l k q
  let R : EnrichedFunctor SSet.{u} (CocartesianIsoTransportCategory A)
      (CocartesianFibrationCategory (nerve A)) :=
    quasicategoryCoreEnrichedFunctor
      (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))
  have h := coherentHomIntervalComparison_uncurry_enriched_naturality R X Y
  rw [cocartesianIsoTransportSource_map_identity, CategoryTheory.Functor.map_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp] at h
  apply intervalMappingUncurry_injective
  rw [cocartesianIsoTransportNativeHomComparison_zero_uncurry,
    cocartesianStraighteningHomInterval_uncurry]
  have hh := congrArg (fun f ↦ f ≫ cocartesianStraighteningCoherentMap A) h
  simp only [coherentHomIntervalComparison, pinchedHomToIntervalMappingSpace_uncurry,
    Category.assoc] at hh ⊢
  exact hh

end SerrePositivity.InfinityCategories
