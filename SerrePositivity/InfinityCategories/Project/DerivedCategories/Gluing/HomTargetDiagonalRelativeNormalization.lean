module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetRelativeNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalPathHomotopyPrism
/-!
概要：元終域の正規化 prism を、元入力付き係数対角の全区間族と両端固定で比較する。
方針：元 Hom 空間から区間 Hom への射で相対 homotopy を送る。
規約：同じ全 path を保つ。使われ方：指定対角境界の係数辺の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetNormalizedIntervalPrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedPrism R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right))

def dgGluingHomTargetCoefficientDiagonalPrism :=
  (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y).h

lemma dgGluingHomTargetCoefficientDiagonalPrism_eq :
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)) =
    dgGluingHomTargetCoefficientDiagonalPrism R C D E p q X Y := by
  change _ = (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalPath R C D E p q X Y)).h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathHomotopy_prism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalPath,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPathComparison_path, uncurry_natural_right]

lemma dgGluingHomTargetDiagonalRelativeNormalization_exists :
    ∃ H : SSet.Homotopy (dgGluingHomTargetNormalizedIntervalPrism R C D E p q X Y)
        (dgGluingHomTargetCoefficientDiagonalPrism R C D E p q X Y),
      (((SSet.boundary 1).ι ▷ P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v}) ⊗ P) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ P) ≫
            dgGluingHomTargetCoefficientDiagonalPrism R C D E p q X Y := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRelativeNormalization_exists R C D E p q X Y
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right))
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H t
  let U := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T rfl
    (dgGluingHomTargetCoefficientDiagonalPrism_eq R C D E p q X Y)
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc,
    dgGluingHomTargetCoefficientDiagonalPrism_eq]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
