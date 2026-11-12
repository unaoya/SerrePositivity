module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapDiagonalPastingFamilies
/-!
概要：元終域の同じ四面体上に係数側の六片を構成し、共有辺と実 cap 対角を回収する。
方針：既知の六再添字を元四面体へ適用する。
規約：元入力と六片の代表を変えない。使われ方：指定対角境界の六角形関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetUnitCollarDiagonalTriangleFamily :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCollarDiagonalTriangleDomain P ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y

def dgGluingHomTargetUnitCapPastingTriangleFamily (i : Fin 6) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain i P ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_first_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 0 =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 1 := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_first_diagonal]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_last_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 2 =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 3 := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_last_diagonal]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_first_bridge :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 1 =
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 5 := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_first_bridge]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_last_bridge :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 3 =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 5 := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_last_bridge]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_first :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 1 =
      (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 4 := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_coefficient_first]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_last :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 3 =
      (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 4 := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_coefficient_last]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_collar_bridge :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 5 =
      (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCollarDiagonalTriangleFamily R C D E p q X Y := by
  simp only [dgGluingHomTargetUnitCapPastingTriangleFamily,
    dgGluingHomTargetUnitCollarDiagonalTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_collar_bridge]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_first_cap :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 0 =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_first_cap]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron_three R C D E p q X Y]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreUnitCapTriangleFamily_reindex R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreUnitCapTriangleFamily_diagonal R C D E p q X Y]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_last_cap :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 2 =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_last_cap]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron_zero R C D E p q X Y]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitUnitCapTriangleFamily_reindex R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitUnitCapTriangleFamily_diagonal R C D E p q X Y]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
