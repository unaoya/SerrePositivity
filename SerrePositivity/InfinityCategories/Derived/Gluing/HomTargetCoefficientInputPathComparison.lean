module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputPath
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetInputPathPullback_kanComplex :
    KanComplex (dgGluingHomTargetInputPathPullback R C D E p q X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  let : KanComplex (dgGluingHomTargetFirstInputFiber R C D E p q X Y) :=
    dgGluingTrivialKanProjection_kanComplex
      (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
  let : KanComplex (dgGluingHomTargetLastInputFiber R C D E p q X Y) :=
    dgGluingTrivialKanProjection_kanComplex
      (dgGluingHomTargetLastInputProjection R C D E p q X Y)
  let := F2.kanComplex_tensor (dgGluingHomTargetLastInputFiber R C D E p q X Y)
    (dgGluingHomTargetFirstInputFiber R C D E p q X Y)
  exact dgGluingKanPathPullback_kanComplex _

def dgGluingHomTargetCoefficientInputPathComparison :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
    dgGluingHomTargetInputPathTransport R C D E p q X Y

lemma dgGluingHomTargetCoefficientInputPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y) := by
  let := dgGluingHomTargetInputPathPullback_kanComplex R C D E p q X Y
  let := F2.kanComplex_tensor
    (complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right))
  let : KanComplex (dgGluingHomTargetCoefficientPathPullback R C D E p q X Y) :=
    dgGluingKanPathPullback_kanComplex _
  have h := (dgGluingHomTargetCoefficientPathComparison_equivalence R C D E p q X Y).isQCatEquivalence.comp
    (dgGluingHomTargetInputPathTransport_equivalence R C D E p q X Y).isQCatEquivalence
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
