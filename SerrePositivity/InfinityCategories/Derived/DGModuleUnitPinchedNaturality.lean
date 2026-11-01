module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingSpaceInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitPostcomposition
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
/-!
概要：R の代表加群からの全 pinched Hom と評価複体との比較は、実閉後合成と可換。
方針：全 Hom の Yoneda 自然性と単位 Hom の自然性を実 pinched 鎖写像の合成則で結ぶ。
規約：全次数・全単体の等式。使われ方：実 augmentation の空間値作用との同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ実 Yoneda 比較は、元の実閉射の後合成と厳密に可換する。 -/
lemma dgHomModuleUnderlyingPinchedIso_naturality {M N : RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N) :
    dgHomModuleUnitPostcomposition R D f ≫ (dgHomModuleUnderlyingPinchedIso R D N).hom =
      (dgHomModuleUnderlyingPinchedIso R D M).hom ≫
        complexPinchedMap.{u, max (u + 1) v} ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) := by
  dsimp only [dgHomModuleUnitPostcomposition, dgHomModuleUnderlyingPinchedIso]
  simp only [asIso_hom, complexPinchedMap]
  rw [← pinchedHomChainMap_comp, ← pinchedHomChainMap_comp]
  congr 1
  have hy := dgYonedaIso_postcompose R PUnit.{1} PUnit.unit
    (M := ForgetEnrichment.of (Complex R) M) (N := ForgetEnrichment.of (Complex R) N) f
  have ht := congrArg (fun q ↦ q ≫ (complexUnitHomIso (N.obj (Opposite.op PUnit.unit))).hom) hy
  calc
    _ = ((dgYonedaIso R PUnit.unit M).hom ≫
          (moduleEvaluation R PUnit.{1} PUnit.unit).map f) ≫
        (complexUnitHomIso (N.obj (Opposite.op PUnit.unit))).hom := by
      simpa only [Category.assoc] using! ht
    _ = _ := by
      have hu := complexUnitHomIso_naturality
        ((moduleEvaluation R PUnit.{1} PUnit.unit).map f)
      have hv := congrArg (fun q ↦ (dgYonedaIso R PUnit.unit M).hom ≫ q) hu.symm
      simpa only [Category.assoc] using! hv
end SerrePositivity.InfinityCategories
