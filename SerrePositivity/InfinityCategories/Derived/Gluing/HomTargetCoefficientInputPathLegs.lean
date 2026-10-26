module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.PathPullbackEndpointLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathHomotopy
/-!
概要：係数側の元入力付き path 比較の全 path と二つの元入力を回収する。
方針：二つの引き戻し輸送の射影則を合成し、元切断と二対角を厳密に照合する。
規約：同じ元 Hom 入力と全 path を保持する。使われ方：指定対角三辺の係数側辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetInputPathProjection :
    dgGluingHomTargetInputPathPullback R C D E p q X Y ⟶
      (ihom (Δ[1] : SSet.{max (u + 1) v})).obj
        (intervalMappingSpace (X := dgNerve R E)
          (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))) :=
  pullback.fst _ _

def dgGluingHomTargetInputPairProjection :
    dgGluingHomTargetInputPathPullback R C D E p q X Y ⟶
      dgGluingHomTargetLastInputFiber R C D E p q X Y ⊗
        dgGluingHomTargetFirstInputFiber R C D E p q X Y :=
  pullback.snd _ _

def dgGluingHomTargetStandardLastInputLift :=
  complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
    dgGluingHomTargetLastInputSection R C D E p q X Y

def dgGluingHomTargetStandardFirstInputLift :=
  complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
    dgGluingHomTargetFirstInputSection R C D E p q X Y

lemma dgGluingHomTargetInputPathTransport_path :
    dgGluingHomTargetInputPathTransport R C D E p q X Y ≫
      dgGluingHomTargetInputPathProjection R C D E p q X Y =
    dgGluingHomTargetCoefficientPathProjection R C D E p q X Y ≫
      (ihom (Δ[1] : SSet.{max (u + 1) v})).map
        (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
          (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))) := by
  rw [dgGluingHomTargetInputPathTransport, dgGluingHomTargetInputPathProjection,
    Category.assoc, dgGluingKanPathInputTransport_path,
    dgGluingKanPathPullbackTransport_path]
  rfl

lemma dgGluingHomTargetCoefficientInputPathComparison_path :
    dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y ≫
      dgGluingHomTargetInputPathProjection R C D E p q X Y =
    dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y ≫
      (ihom (Δ[1] : SSet.{max (u + 1) v})).map
        (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
          (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))) := by
  rw [dgGluingHomTargetCoefficientInputPathComparison, Category.assoc,
    dgGluingHomTargetInputPathTransport_path, ← Category.assoc,
    dgGluingHomTargetCoefficientPathComparison_path]

lemma dgGluingHomTargetInputPathTransport_inputs :
    dgGluingHomTargetInputPathTransport R C D E p q X Y ≫
      dgGluingHomTargetInputPairProjection R C D E p q X Y =
    dgGluingHomTargetCoefficientInputProjection R C D E p q X Y ≫
      dgGluingHomTargetInputPairSection R C D E p q X Y := by
  rw [dgGluingHomTargetInputPathTransport, dgGluingHomTargetInputPairProjection,
    Category.assoc, dgGluingKanPathInputTransport_inputs, ← Category.assoc,
    dgGluingKanPathPullbackTransport_inputs]
  rfl

lemma dgGluingHomTargetCoefficientInputPathComparison_inputs :
    dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y ≫
      dgGluingHomTargetInputPairProjection R C D E p q X Y =
    lift (dgGluingHomTargetStandardLastInputLift R C D E p q X Y)
      (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y) := by
  rw [dgGluingHomTargetCoefficientInputPathComparison, Category.assoc,
    dgGluingHomTargetInputPathTransport_inputs, ← Category.assoc,
    dgGluingHomTargetCoefficientPathComparison_inputs]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingHomTargetHomInputPair, dgGluingHomTargetInputPairSection,
      dgGluingHomTargetStandardLastInputLift, Category.assoc, tensorHom_fst,
      lift_fst_assoc, lift_fst]
  · simp only [dgGluingHomTargetHomInputPair, dgGluingHomTargetInputPairSection,
      dgGluingHomTargetStandardFirstInputLift, Category.assoc, tensorHom_snd,
      lift_snd_assoc, lift_snd]

def dgGluingHomTargetCoefficientDiagonalPath :=
  dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y ≫
    dgGluingHomTargetInputPathProjection R C D E p q X Y

lemma dgGluingHomTargetCoefficientDiagonalPath_start :
    dgGluingHomTargetCoefficientDiagonalPath R C D E p q X Y ≫
      (F2.intervalEndpointNatTrans 0).app _ =
    dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y := by
  let c := dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y
  let proj := dgGluingHomTargetInputPairProjection R C D E p q X Y
  let d := dgGluingHomTargetLastInputDiagonal R C D E p q X Y
  have h := congrArg (fun k => c ≫ k)
    (dgGluingPathPullback_start
      (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
      (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
  have hc : c ≫ proj ≫ fst
      (dgGluingHomTargetLastInputFiber R C D E p q X Y)
      (dgGluingHomTargetFirstInputFiber R C D E p q X Y) ≫ d =
      dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫ d := by
    have hh := congrArg (fun k => k ≫ fst
        (dgGluingHomTargetLastInputFiber R C D E p q X Y)
        (dgGluingHomTargetFirstInputFiber R C D E p q X Y) ≫ d)
      (dgGluingHomTargetCoefficientInputPathComparison_inputs R C D E p q X Y)
    simpa only [Category.assoc, lift_fst_assoc] using hh
  exact (Category.assoc _ _ _).trans (h.trans hc)

lemma dgGluingHomTargetCoefficientDiagonalPath_end :
    dgGluingHomTargetCoefficientDiagonalPath R C D E p q X Y ≫
      (F2.intervalEndpointNatTrans 1).app _ =
    dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y := by
  let c := dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y
  let proj := dgGluingHomTargetInputPairProjection R C D E p q X Y
  let d := dgGluingHomTargetFirstInputDiagonal R C D E p q X Y
  have h := congrArg (fun k => c ≫ k)
    (dgGluingPathPullback_end
      (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
      (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
  have hc : c ≫ proj ≫ snd
      (dgGluingHomTargetLastInputFiber R C D E p q X Y)
      (dgGluingHomTargetFirstInputFiber R C D E p q X Y) ≫ d =
      dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫ d := by
    have hh := congrArg (fun k => k ≫ snd
        (dgGluingHomTargetLastInputFiber R C D E p q X Y)
        (dgGluingHomTargetFirstInputFiber R C D E p q X Y) ≫ d)
      (dgGluingHomTargetCoefficientInputPathComparison_inputs R C D E p q X Y)
    simpa only [Category.assoc, lift_snd_assoc] using hh
  exact (Category.assoc _ _ _).trans (h.trans hc)

def dgGluingHomTargetCoefficientDiagonalHomotopy :
    SSet.Homotopy
      (dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
        dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
      (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
        dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) :=
  stableHomotopyRetarget
    (dgGluingIntervalPathHomotopy (dgGluingHomTargetCoefficientDiagonalPath R C D E p q X Y))
    (dgGluingHomTargetCoefficientDiagonalPath_start R C D E p q X Y)
    (dgGluingHomTargetCoefficientDiagonalPath_end R C D E p q X Y)

end SerrePositivity.InfinityCategories
