module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputDiagonals
public import SerrePositivity.InfinityCategories.Derived.Gluing.KanPathInputTransport
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence
/-!
概要：元終域の係数 path を元入力付き二合成対応の対角 path へ輸送する。
方針：実 Hom から区間 Hom への同値と、元左右入力の切断同値を合成する。
規約：全 path と元入力を保持する。使われ方：元 lax Hom 比較の実逆への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (KST.SConstruction.dgHomGluingBimodule R C D E p q))

attribute [local irreducible] KST.SConstruction.dgHomGluingBimodule

def dgGluingHomTargetInputPathPullback : SSet.{max (u + 1) v} :=
  pullback (F2.arrowEndpointPair (intervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))))
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y ⊗ₘ
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)

def dgGluingHomTargetInputPathTransport :
    dgGluingHomTargetCoefficientPathPullback R C D E p q X Y ⟶
      dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  dgGluingKanPathPullbackTransport
    (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right)))
    (dgGluingHomTargetCoefficientInputPair R C D E p q X Y) ≫
  dgGluingKanPathInputTransport _
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y ⊗ₘ
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetInputPairSection R C D E p q X Y)
    (dgGluingHomTargetInputPairSection_diagonals R C D E p q X Y)

lemma dgGluingHomTargetInputPathTransport_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingHomTargetInputPathTransport R C D E p q X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  let : KanComplex (dgGluingHomTargetFirstInputFiber R C D E p q X Y) :=
    dgGluingTrivialKanProjection_kanComplex
      (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
  let : KanComplex (dgGluingHomTargetLastInputFiber R C D E p q X Y) :=
    dgGluingTrivialKanProjection_kanComplex
      (dgGluingHomTargetLastInputProjection R C D E p q X Y)
  let := F2.kanComplex_tensor
    (complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right))
  let := F2.kanComplex_tensor (dgGluingHomTargetLastInputFiber R C D E p q X Y)
    (dgGluingHomTargetFirstInputFiber R C D E p q X Y)
  have hp : KanComplex (dgGluingHomTargetCoefficientPathPullback R C D E p q X Y) :=
    dgGluingKanPathPullback_kanComplex _
  dsimp only [dgGluingHomTargetCoefficientPathPullback, DGNerve.pinchedHom] at hp
  let := dgGluingKanPathPullback_kanComplex
    (dgGluingHomTargetCoefficientInputPair R C D E p q X Y ≫
      (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
          (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right)) ⊗ₘ
        pinchedHomToIntervalMappingSpace (X := dgNerve R E)
          (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))))
  let : KanComplex (dgGluingHomTargetInputPathPullback R C D E p q X Y) :=
    dgGluingKanPathPullback_kanComplex _
  exact (dgGluingKanPathPullbackTransport_equivalence _ _
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence
      (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
      (Simplex.vertex (q.obj Y.right))).isSimplicialHomotopyEquivalence).comp
    (dgGluingKanPathInputTransport_equivalence _ _ _
      (dgGluingHomTargetInputPairSection_diagonals R C D E p q X Y)
      (dgGluingHomTargetInputPairSection_equivalence R C D E p q X Y))

end SerrePositivity.InfinityCategories
