module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCoefficientActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedPostcompositionAW
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedConstantIntervalFamilies
/-!
概要：元二脚の左右 Hom 入力と実 augmentation の合成三角形を元終域に構成する。
方針：実 dg 合成 prism を使い、全三辺を同じ二作用へ照合する。
規約：標準三角形の全族を保持する。使われ方：元終域の入力付き合成対応。
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
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetLeftIntervalInput :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCoefficientInput R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetRightIntervalInput :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCoefficientInput R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetLeftCompositionTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCoefficientInput R C D E p q X Y)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q Y)))

def dgGluingHomTargetRightCompositionTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R E
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q X)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCoefficientInput R C D E p q X Y)

lemma dgGluingHomTargetLeftCompositionTriangle_variable :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_two R E _ _

lemma dgGluingHomTargetRightCompositionTriangle_variable :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingHomTargetRightIntervalInput R C D E p q X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_zero R E _ _

lemma dgGluingHomTargetLeftCompositionTriangle_fixed :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y =
    CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace (homObject R C X.left Y.left)) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E
          (dgHomGluingTargetMap R C D E p q Y)).edge := by
  rw [dgGluingHomTargetLeftCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_zero,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedConstantIntervalFamily]
  rfl

lemma dgGluingHomTargetRightCompositionTriangle_fixed :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y =
    CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace (homObject R D X.right Y.right)) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E
          (dgHomGluingTargetMap R C D E p q X)).edge := by
  rw [dgGluingHomTargetRightCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_two,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedConstantIntervalFamily]
  rfl

lemma dgGluingHomTargetLeftCompositionTriangle_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingHomTargetLeftCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_one,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositionFamily_closed_post,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCoefficientAction, Category.assoc]

lemma dgGluingHomTargetRightCompositionTriangle_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingHomTargetRightCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_one,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositionFamily_closed_pre,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCoefficientAction, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
