module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowCompositionInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.StrictPathPullbackEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedLastInputDiagonalFibration
/-!
概要：指定元比較の共通対角を、元二入力付き厳密 pullback と全 path 模型に保存する。
方針：元矢印 Hom の二三角形の共通対角を使い、定値 path を付ける。
規約：比較の実作用と元左右入力を保持する。使われ方：係数 path 比較の実逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y

attribute [local irreducible] dgHomGluingBimodule

section
attribute [local irreducible] dgGluingHomTargetLastInputDiagonal dgGluingHomTargetFirstInputDiagonal

def dgGluingHomTargetInputStrictPullback : SSet.{max (u + 1) v} := by
  letI : Limits.HasLimit (cospan (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
      (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)) :=
    HasLimitsOfShape.has_limit _
  exact pullback (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

end

def dgGluingHomTargetInputStrictPathComparison :
    dgGluingHomTargetInputStrictPullback R C D E p q X Y ⟶
      dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  dgGluingStrictPathPullbackMap _ _

lemma dgGluingHomTargetArrowInputLift_diagonals :
    dgGluingHomTargetArrowLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y =
    dgGluingHomTargetArrowFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y := by
  dsimp only [dgGluingHomTargetLastInputDiagonal, dgGluingHomTargetFirstInputDiagonal,
    dgGluingHomTargetArrowLastInputLift, dgGluingHomTargetArrowFirstInputLift]
  simp only [pullback.lift_fst_assoc]
  have hh := congrArg (fun k => dgGluingHomTargetArrowCompositionComparison R C D E p q X Y ≫ k)
    (pullback.condition
      (f := dgGluingFirstFixedCompositionDiagonal
        (Edge.ofTruncated (X := dgNerve R E)
          (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
        (Simplex.vertex (q.obj Y.right)))
      (g := compositionCorrespondenceDiagonal (X := dgNerve R E)
        (Simplex.vertex (p.obj X.left))
        (Edge.ofTruncated (X := dgNerve R E)
          (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))))
  simpa only [dgGluingHomTargetArrowFirstComposition, dgGluingHomTargetArrowLastComposition,
    Category.assoc, ForgetEnrichment.to_of] using hh.symm

def dgGluingHomTargetArrowInputStrictComparison :
    P ⟶ dgGluingHomTargetInputStrictPullback R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
    (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y)
    (dgGluingHomTargetArrowInputLift_diagonals R C D E p q X Y)

def dgGluingHomTargetArrowInputPathComparison :
    P ⟶ dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  dgGluingHomTargetArrowInputStrictComparison R C D E p q X Y ≫
    dgGluingHomTargetInputStrictPathComparison R C D E p q X Y

lemma dgGluingHomTargetInputStrictPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetInputStrictPathComparison R C D E p q X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  have hf : KanComplex (dgGluingHomTargetFirstInputFiber R C D E p q X Y) :=
    dgGluingTrivialKanProjection_kanComplex
      (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
  have hl : KanComplex (dgGluingHomTargetLastInputFiber R C D E p q X Y) :=
    dgGluingTrivialKanProjection_kanComplex
      (dgGluingHomTargetLastInputProjection R C D E p q X Y)
  have hf' := hf
  have hl' := hl
  dsimp only [dgGluingHomTargetFirstInputFiber] at hf'
  dsimp only [dgGluingHomTargetLastInputFiber] at hl'
  have : Fibration (dgGluingHomTargetLastInputDiagonal R C D E p q X Y) :=
    dgGluingLastFixedInputDiagonal_fibration (X := dgNerve R E)
      (Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
      (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)
  exact dgGluingStrictPathPullbackMap_equivalence
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

end SerrePositivity.InfinityCategories
