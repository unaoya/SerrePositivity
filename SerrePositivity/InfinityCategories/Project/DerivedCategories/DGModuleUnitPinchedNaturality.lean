module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnderlyingSpaceInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnitPostcomposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ実 Yoneda 比較は、元の実閉射の後合成と厳密に可換する。 -/
lemma dgHomModuleUnderlyingPinchedIso_naturality {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitPostcomposition R D f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnderlyingPinchedIso R D N).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnderlyingPinchedIso R D M).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} ((moduleEvaluation R PUnit.{1} PUnit.unit).map f) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitPostcomposition, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnderlyingPinchedIso]
  simp only [asIso_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp]
  congr 1
  have hy := _root_.SerrePositivity.DifferentialGraded.dgYonedaIso_postcompose R PUnit.{1} PUnit.unit
    (M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M) (N := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) f
  have ht := congrArg (fun q ↦ q ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (N.obj (Opposite.op PUnit.unit))).hom) hy
  calc
    _ = ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R PUnit.unit M).hom ≫
          (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R PUnit.{1} PUnit.unit).map f) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (N.obj (Opposite.op PUnit.unit))).hom := by
      simpa only [Category.assoc] using! ht
    _ = _ := by
      have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R PUnit.{1} PUnit.unit).map f)
      have hv := congrArg (fun q ↦ (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R PUnit.unit M).hom ≫ q) hu.symm
      simpa only [Category.assoc] using! hv
end SerrePositivity.InfinityCategories.Project.DerivedCategories
