module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputPathPoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalBoundaryFilling
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyTriangleFillingSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputPathEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedInputStrictKanComplex
/-!
概要：元入力付き path 比較の同値性を厳密共通対角模型へ戻す。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetInputStrictPullback_kanComplex :
    KanComplex (dgGluingHomTargetInputStrictPullback R C D E p q X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  have hf := dgGluingTrivialKanProjection_kanComplex
    (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
  have hfAlias : KanComplex (dgGluingHomTargetFirstInputFiber R C D E p q X Y) := hf
  have : Fibration (dgGluingHomTargetLastInputDiagonal R C D E p q X Y) :=
    dgGluingLastFixedInputDiagonal_fibration (X := dgNerve R E)
      (Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
      (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)
  exact dgGluingKanPullback_of_leftFibration
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

lemma dgGluingHomTargetArrowInputStrictComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetArrowInputStrictComparison R C D E p q X Y) := by
  have := dgGluingHomTargetInputStrictPullback_kanComplex R C D E p q X Y
  have := dgGluingHomTargetInputPathPullback_kanComplex R C D E p q X Y
  have he := dgGluingHomTargetInputStrictPathComparison_equivalence R C D E p q X Y
  have hc : IsQCatEquivalence (dgGluingHomTargetArrowInputStrictComparison R C D E p q X Y ≫
      dgGluingHomTargetInputStrictPathComparison R C D E p q X Y) :=
    (dgGluingHomTargetArrowInputPathComparison_equivalence R C D E p q X Y).isQCatEquivalence
  exact (he.isQCatEquivalence.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
