# HT04：検証した終点の型

全追加宣言の型は `ht04-law-types.json`（379件、欠落0）。

## universalOrientedPrism_affineLine_resolvedCover_quasiIso

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)]
  (η :
    Quiver.Hom.{u, u + 1}
      (SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison.affineLineFormalModel.{u}
        (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
      (SerrePositivity.BhattScholze.Prismatic.affineHTTotalComplex.{u}
        (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) ⋯ 1)),
  Eq.{u + 1}
      (CategoryTheory.CategoryStruct.comp.{u, u + 1}
        (CategoryTheory.Iso.hom.{u, u + 1}
          (SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison.affineLineFormalZeroIso.{u}
            (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)))
        (HomologicalComplex.homologyMap.{u, u + 1, 0} η 0))
      (ModuleCat.ofHom.{u, u}
        (SerrePositivity.BhattScholze.Prismatic.affineHTTotalMap.{u}
          (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) ⋯ 1 0)) →
    Eq.{u + 1}
        (CategoryTheory.CategoryStruct.comp.{u, u + 1}
          (CategoryTheory.Iso.hom.{u, u + 1}
            (SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison.affineLineFormalOneIso.{u}
              (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)))
          (HomologicalComplex.homologyMap.{u, u + 1, 0} η 1))
        (ModuleCat.ofHom.{u, u}
          (SerrePositivity.BhattScholze.Prismatic.affineHTTotalMap.{u}
            (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) ⋯ 1 1)) →
      QuasiIso.{u, u + 1, 0}
        (CategoryTheory.Functor.map.{u, u, u + 1, u + 1}
          (SerrePositivity.BhattScholze.Prismatic.Construction61.completedCoverModelFunctor.{u}
            (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
          (CategoryTheory.Functor.map.{u, u, u + 1, u + 1}
            (SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution.complexResolutionFunctor.{u}
              ↑(SerrePositivity.BhattScholze.UniversalOrientedPrismRing.{u} p))
            (CategoryTheory.Functor.map.{u, u, u + 1, u + 1}
              (SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison.affineRestrictedComplexFunctor.{u, u}
                (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) 1)
              η)))
```

## universalOrientedPrism_affineLine_moduleComparison

```lean
∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
  Function.Bijective.{u + 1, u + 1}
      ⇑(SerrePositivity.BhattScholze.Prismatic.hodgeTateMapZero.{u}
          (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) ⋯ 1) ∧
    Function.Bijective.{u + 1, u + 1}
        ⇑(SerrePositivity.BhattScholze.Prismatic.hodgeTateMapOne.{u}
            (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) ⋯ 1) ∧
      ∀ (i : ℕ),
        LT.lt.{0} 1 i →
          Subsingleton.{u + 1}
            (SerrePositivity.BhattScholze.Prismatic.hodgeTateCohomology'.{u}
              (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p) ⋯ 1 i)
```
