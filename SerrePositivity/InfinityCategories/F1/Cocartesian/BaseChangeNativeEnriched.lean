module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportInfinity
public import SerrePositivity.InfinityCategories.F1.CoreEnrichedComposition

/-!
概要：元の二重底変換の全相対 Hom 作用を、同じ指定結合同型の豊穣圏へ束ねる。
方針：始域の全 Hom がそのままであることを使い、既存の二重底変換を使う。
規約：元の全 Hom 作用と既存の結合同型を保持する。
使われ方：全局所比較の族と元の大域結合比較の族を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の二重底変換作用を、同じ指定結合同型を持つ対象の全 Hom へ束ねる。 -/
def cocartesianBaseChangeNativeEnriched
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    EnrichedFunctor SSet.{u} (CocartesianFibrationObject (nerve C))
      (IsoTransportObject (CocartesianFibrationObject (nerve A))) where
  obj p := cocartesianBaseChangeIsoTransportObject l k p
  map p q := ((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
    (cocartesianFibrationBaseChangeEnriched (nerveMap l))).map p q
  map_id p := ((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
    (cocartesianFibrationBaseChangeEnriched (nerveMap l))).map_id p
  map_comp p q r := ((cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
    (cocartesianFibrationBaseChangeEnriched (nerveMap l))).map_comp p q r

/-- 同じ元の二重底変換 Hom の core を持つ、指定結合同型の豊穣関手。 -/
def cocartesianBaseChangeNativeCoreEnriched
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    EnrichedFunctor SSet.{u} (CocartesianFibrationCategory (nerve C))
      (CocartesianIsoTransportCategory A) :=
  quasicategoryCoreEnrichedFunctor (cocartesianBaseChangeNativeEnriched l k)

/-- 始域を評価すると、元の全相対 Hom に作用する二重底変換の豊穣関手そのもの。 -/
lemma cocartesianBaseChangeNativeEnriched_source
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    (cocartesianBaseChangeNativeEnriched l k).comp SSet
      (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A))) =
    (cocartesianFibrationBaseChangeEnriched (nerveMap k)).comp SSet
      (cocartesianFibrationBaseChangeEnriched (nerveMap l)) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  exact Category.comp_id _

end SerrePositivity.InfinityCategories
