module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.TrivialKanSectionEquivalence
/-!
概要：元二脚の左右入力を保持する二つの合成対応と実入力 fiber を構成する。
方針：元終域の標準三角形を持ち上げ、元 Hom 入力に沿って引き戻す。
規約：実射・全三角形・元入力を回収する。使われ方：元 lax Hom の相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetFirstComposition :=
  dgGluingFirstFixedCompositionLift.{max (u + 1) v} (X := dgNerve R E)
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (Simplex.vertex (q.obj Y.right))
    (dgGluingHomTargetRightIntervalInput R C D E p q X Y)
    (dgGluingHomTargetRightCompositionTriangle R C D E p q X Y)
    (dgGluingHomTargetRightCompositionTriangle_fixed R C D E p q X Y)
    (dgGluingHomTargetRightCompositionTriangle_variable R C D E p q X Y)

def dgGluingHomTargetLastComposition :=
  dgGluingLastFixedCompositionLift.{max (u + 1) v} (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)
    (dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y)
    (dgGluingHomTargetLeftCompositionTriangle_variable R C D E p q X Y)
    (dgGluingHomTargetLeftCompositionTriangle_fixed R C D E p q X Y)

def dgGluingHomTargetFirstInputFiber :=
  pullback
    (dgGluingFirstFixedCompositionSecond.{max (u + 1) v} (X := dgNerve R E)
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (Simplex.vertex (q.obj Y.right)))
    (dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetLastInputFiber :=
  pullback
    (compositionCorrespondenceFirst.{max (u + 1) v} (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

def dgGluingHomTargetFirstInputProjection :=
  pullback.snd
    (dgGluingFirstFixedCompositionSecond.{max (u + 1) v} (X := dgNerve R E)
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (Simplex.vertex (q.obj Y.right)))
    (dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetLastInputProjection :=
  pullback.snd
    (compositionCorrespondenceFirst.{max (u + 1) v} (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetFirstInputProjection_trivialKanFibration :
    TrivialKanFibration (dgGluingHomTargetFirstInputProjection R C D E p q X Y) := by
  let : TrivialKanFibration (dgGluingFirstFixedCompositionSecond.{max (u + 1) v} (X := dgNerve R E)
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (Simplex.vertex (q.obj Y.right))) :=
    dgGluingFirstFixedCompositionSecond_trivialKanFibration _ _
  exact trivialKanFibration_pullback_snd _ _

lemma dgGluingHomTargetLastInputProjection_trivialKanFibration :
    TrivialKanFibration (dgGluingHomTargetLastInputProjection R C D E p q X Y) := by
  let : TrivialKanFibration (compositionCorrespondenceFirst.{max (u + 1) v} (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))) :=
    compositionCorrespondenceFirst_trivialKanFibration _ _
  exact trivialKanFibration_pullback_snd _ _

def dgGluingHomTargetFirstInputSection :
    complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) ⟶
      dgGluingHomTargetFirstInputFiber R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetFirstComposition R C D E p q X Y) (𝟙 _)
    ((dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _).trans
      (Category.id_comp _).symm)

def dgGluingHomTargetLastInputSection :
    complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⟶
      dgGluingHomTargetLastInputFiber R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetLastComposition R C D E p q X Y) (𝟙 _)
    ((dgGluingLastFixedCompositionLift_first _ _ _ _ _ _).trans
      (Category.id_comp _).symm)

lemma dgGluingHomTargetFirstInputSection_input :
    dgGluingHomTargetFirstInputSection R C D E p q X Y ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetLastInputSection_input :
    dgGluingHomTargetLastInputSection R C D E p q X Y ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetFirstInputSection_composition :
    dgGluingHomTargetFirstInputSection R C D E p q X Y ≫
      pullback.fst
        (dgGluingFirstFixedCompositionSecond (X := dgNerve R E)
          (Edge.ofTruncated (X := dgNerve R E)
            (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
          (Simplex.vertex (q.obj Y.right)))
        (dgGluingHomTargetRightIntervalInput R C D E p q X Y) =
      dgGluingHomTargetFirstComposition R C D E p q X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomTargetLastInputSection_composition :
    dgGluingHomTargetLastInputSection R C D E p q X Y ≫
      pullback.fst
        (compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
          (Edge.ofTruncated (X := dgNerve R E)
            (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
        (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) =
      dgGluingHomTargetLastComposition R C D E p q X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomTargetFirstInputSection_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingHomTargetFirstInputSection R C D E p q X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  exact dgGluingTrivialKanSection_equivalence
    (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
    (dgGluingHomTargetFirstInputSection R C D E p q X Y)
    (dgGluingHomTargetFirstInputSection_input R C D E p q X Y)

lemma dgGluingHomTargetLastInputSection_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingHomTargetLastInputSection R C D E p q X Y) := by
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  exact dgGluingTrivialKanSection_equivalence
    (dgGluingHomTargetLastInputProjection R C D E p q X Y)
    (dgGluingHomTargetLastInputSection R C D E p q X Y)
    (dgGluingHomTargetLastInputSection_input R C D E p q X Y)

end SerrePositivity.InfinityCategories
