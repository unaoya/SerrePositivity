module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCoefficientActions
/-!
概要：元終域内の係数 path 比較の実ホモトピー逆と両往復則。
方針：検証済みの同じ実比較のホモトピー同値性から逆射と全単体ホモトピーを取る。
規約：lax Hom 比較全体の逆射とは区別する。左右入力を忘れた比較へ置換しない。
使われ方：二つの合成三角形を持つ lax Hom 標的への輸送の始点。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetCoefficientPathComparisonInverse :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathPullback R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison_equivalence R C D E p q X Y).choose

def dgGluingHomTargetCoefficientPathComparisonInverse_unit :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
      dgGluingHomTargetCoefficientPathComparisonInverse R C D E p q X Y)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))) :=
  (Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison_equivalence R C D E p q X Y)).1.some

def dgGluingHomTargetCoefficientPathComparisonInverse_counit :
    SSet.Homotopy (dgGluingHomTargetCoefficientPathComparisonInverse R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison R C D E p q X Y)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathPullback R C D E p q X Y)) :=
  (Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison_equivalence R C D E p q X Y)).2.some

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
