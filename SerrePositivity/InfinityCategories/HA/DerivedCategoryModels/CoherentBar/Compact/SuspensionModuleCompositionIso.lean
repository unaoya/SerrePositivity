module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionConeComparisonCore
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition

/-!
概要：二回の実加群延長と合成入力の実延長を、全 Hom 自然な同じ閉同型で比較する。
方針：小さい源の評価で前合成し、元の合成比較の全 Hom 自然性を使う。
規約：固定 cell 分解・商への比較の存在はここでは主張しない。
使われ方：固定 data の合成の cone 評価比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t s
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R]

/-- 実加群延長の合成比較を、任意の小さい源で前合成して同じ end に保持する。 -/
def dgModuleCompositionPrecompositionIso
    (A : Type v) [DGCategory R A] [Small.{u} A]
    (B : Type w) [DGCategory R B] [Small.{u} B]
    (C : Type t) [DGCategory R C] [Small.{u} C]
    (F : DGFunctor R A B) (G : DGFunctor R B C)
    {X : Type s} [DGCategory R X] [Small.{u} X]
    (E : DGFunctor R X (RightModule R A)) :
    ForgetEnrichment.of (Complex R)
      ((E.comp (dgModuleExtension R A B F)).comp (dgModuleExtension R B C G)) ≅
      ForgetEnrichment.of (Complex R) (E.comp (dgModuleExtension R A C (F.comp G))) :=
  dgFunctorClosedIsoFromFamily R X (RightModule R C) _ _
    (fun x => dgModuleExtensionCompositionAt R A B C F G (E.obj x)) (fun x y => by
      change ((E.map x y ≫ (dgModuleExtension R A B F).map _ _) ≫
          (dgModuleExtension R B C G).map _ _) ≫ moduleHomPostcompose R C _ _ _
            (dgModuleExtensionCompositionAt R A B C F G (E.obj y)).hom =
        (E.map x y ≫ (dgModuleExtension R A C (F.comp G)).map _ _) ≫
          moduleHomPrecompose R C _ _ _
            (dgModuleExtensionCompositionAt R A B C F G (E.obj x)).hom
      simpa only [DGFunctor.comp, EnrichedFunctor.comp, Category.assoc] using
        congrArg (fun h => E.map x y ≫ h)
        (dgModuleExtensionCompositionAt_naturality R A B C F G (E.obj x) (E.obj y)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
