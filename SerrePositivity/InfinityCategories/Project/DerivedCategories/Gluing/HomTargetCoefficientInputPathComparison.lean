module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputPath
/-!
概要：元 Hom 複体から、元二入力付き係数対角 path への実同値を構成する。
方針：同じ係数 path 比較と入力付き合成対応への輸送を合成する。
規約：指定 lax 比較そのものとの相対 homotopy は別工程として区別する。
使われ方：指定比較へ同じ実逆と往復則を移す際の係数側比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetInputPathPullback_kanComplex :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathPullback R C D E p q X Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputFiber R C D E p q X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTrivialKanProjection_kanComplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputProjection R C D E p q X Y)
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTrivialKanProjection_kanComplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputProjection R C D E p q X Y)
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputFiber R C D E p q X Y)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _

def dgGluingHomTargetCoefficientInputPathComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathTransport R C D E p q X Y

lemma dgGluingHomTargetCoefficientInputPathComparison_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y) := by
  let := dgGluingHomTargetInputPathPullback_kanComplex R C D E p q X Y
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right))
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathPullback R C D E p q X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientPathComparison_equivalence R C D E p q X Y).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathTransport_equivalence R C D E p q X Y).isQCatEquivalence
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
