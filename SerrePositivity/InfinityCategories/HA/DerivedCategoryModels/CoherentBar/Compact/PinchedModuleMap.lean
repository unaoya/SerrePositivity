module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedHomModule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedChainMapComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.ModuleSphereNaturality
/-!
概要：元の Hom 鎖写像の pinched 空間への作用を単体的加群の射へ持ち上げる。
方針：小さい線形単体への作用を、実 pinched 単体の座標同型で共役する。
規約：元の全単体と鎖写像を保持し、対象の Small 性は要求しない。
使われ方：実評価の脚と Moore ホモロジーチャートの自然性を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  {x y : D} {a b : E}

/-- 小さい線形 Hom 模型への、元の鎖写像の全単体的加群作用。 -/
def dgBarCompactLinearHomModuleMap (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := R) a b where
  app _ := ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ)
  naturality {m n} α := by
    ext s
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_pullback φ α.unop.toOrderHom s

/-- 実 pinched 空間の線形化に載った、同じ鎖写像の作用。 -/
def dgBarCompactPinchedModuleMap (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) a b :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleCoordinateIso (S := R) x y).hom ≫
    Functor.whiskerRight (dgBarCompactLinearHomModuleMap φ) (ModuleCat.uliftFunctor.{v} R) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleCoordinateIso (S := R) a b).inv

lemma dgBarCompactPinchedModuleMap_coordinate
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    dgBarCompactPinchedModuleMap φ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleCoordinateIso (S := R) a b).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleCoordinateIso (S := R) x y).hom ≫
        Functor.whiskerRight (dgBarCompactLinearHomModuleMap φ)
          (ModuleCat.uliftFunctor.{v} R) := by
  simp only [dgBarCompactPinchedModuleMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 忘却後の射は元の実 pinched 写像と、全単体で厳密に一致する。 -/
lemma dgBarCompactPinchedModuleMap_forget
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (dgBarCompactPinchedModuleMap φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) a b).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ := by
  ext n s
  rw [NatTrans.comp_app, NatTrans.comp_app]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) a b).hom.app n
    ((dgBarCompactPinchedModuleMap φ).app n s) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ).app n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) x y).hom.app n s)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso_apply]
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCoordinateEquiv (S := R) a b n).injective
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCoordinateModuleIso (S := R) x y n).hom ≫
      (ModuleCat.uliftFunctor.{v} R).map ((dgBarCompactLinearHomModuleMap φ).app n) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCoordinateModuleIso (S := R) a b n).inv) s)) =
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ s))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCoordinateLinearEquiv (S := R) a b n)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCoordinateLinearEquiv (S := R) a b n).symm
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s)))) = _
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCoordinateLinearEquiv (S := R) a b n).apply_symm_apply _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
