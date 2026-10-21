module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeFamily
public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportHomPath
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityHomPath

/-!
概要：全局所結合比較の可逆 path の族は、元の全 Hom 上で既存の大域結合 path と一致。
方針：同じ区間族の一致を包含の単射性で反映する。
規約：元の path の全族と指定辺を保持する。
使われ方：結合 Hom 比較の全局所版と元の大域版を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom 作用上で、全局所比較の同じ可逆 path は元の結合 path そのもの。 -/
lemma cocartesianBaseChangeNativeInfinityMap_homPath
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) :
    cocartesianBaseChangeNativeInfinityMap l k ≫ cocartesianIsoTransportHomPath A =
      cocartesianBaseChangeAssociativityHomPath l k := by
  have : Mono (equivalencePathι
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))) := by
    unfold equivalencePathι
    infer_instance
  apply (cancel_mono (equivalencePathι _)).mp
  rw [Category.assoc, cocartesianIsoTransportHomPath_ι,
    cocartesianBaseChangeAssociativityHomPath_ι]
  change cocartesianBaseChangeNativeInfinityMap l k ≫
    (cocartesianIsoTransportFamily A ≫ qCatDiagramArrowCurry A) =
      cocartesianBaseChangeAssociativityFamily l k ≫ qCatDiagramArrowCurry A
  rw [← Category.assoc, cocartesianBaseChangeNativeInfinityMap_family]

end SerrePositivity.InfinityCategories
