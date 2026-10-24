module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightNaturalitySquare

/-!
概要：元の A 遷移と fⱼ、fᵢ と B 遷移の合成自然性を、同じ共通底上で実際に比較する。
方針：元の分子を固定し、f の自然性で二因子分解を同じ合成射へそろえる。
規約：比較二重経路を追加入力しない。使われ方：Γ の右像貼合せへの実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightNaturalityComposite : (A.obj i).obj ⟶ (B.obj j).obj :=
  (A.transition hj).hom ≫ (f.app j).hom

def postnikovCommonRightNaturalityCompositeLayer :
    Bimod (postnikovCommonClassBase R hn f c d) (postnikovCommonClassBase R hn f c d) :=
  bimoduleRestrict ((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
    postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) n)
    (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1)

def postnikovCommonRightNaturalityCompositeSource : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R (postnikovCommonClassBase R hn f c d)))) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj) :=
  postnikovCellFactorizationCommonSource R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj)

def postnikovCommonRightNaturalityCompositeTarget : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R (postnikovCommonClassBase R hn f c d)))) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj) :=
  postnikovCellFactorizationCommonTarget R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj)

def postnikovCommonRightNaturalityViaA : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R hn f c d))
    (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R hn f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R hn f c d hj) :=
  postnikovCellFactorizationCommonWitness R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj
    (A.transition hj).hom (f.app j).hom rfl

def postnikovCommonRightNaturalityViaB : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R hn f c d))
    (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R hn f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R hn f c d hj) :=
  postnikovCellFactorizationCommonWitness R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (B.obj i).obj
    (f.app i).hom (B.transition hj).hom (congrArg (fun t => t.hom) (f.naturality hj)).symm

def postnikovCommonRightCompositeSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightNaturalityViaA R hn f c d hj)
    (postnikovCommonRightNaturalityViaB R hn f c d hj) :=
  postnikovCellFactorizationCommonSquare R (A.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovCommonRightNaturalityComposite R f hj) (A.obj j).obj (B.obj i).obj
    (A.transition hj).hom (f.app j).hom rfl
    (f.app i).hom (B.transition hj).hom (congrArg (fun t => t.hom) (f.naturality hj)).symm

def postnikovCommonRightCompositeTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
      (postnikovCommonRightNaturalityViaA R hn f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
      (postnikovCommonRightNaturalityViaB R hn f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightCompositeSquare R hn f c d hj)

lemma postnikovCommonRightCompositeTransportHomotopy_left :
    (postnikovCommonRightCompositeTransportHomotopy R hn f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeLeft
        (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R hn f c d hj)) =
    SquareZeroExtension.relativeLeft (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R hn f c d hj) ≫
      Path.diagonal R (cellResolution R (cellResolution R (cellResolution R
        (cellResolution R (postnikovCommonClassBase R hn f c d))))) :=
  SquareZeroExtension.transportHomotopy_left _ (postnikovCommonRightCompositeSquare R hn f c d hj)

lemma postnikovCommonRightCompositeTransportHomotopy_right :
    (postnikovCommonRightCompositeTransportHomotopy R hn f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeRight
        (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R hn f c d hj)) =
    SquareZeroExtension.relativeRight (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R hn f c d hj) ≫
      Path.diagonal R (postnikovCommonClassBase R hn f c d) :=
  SquareZeroExtension.transportHomotopy_right _ (postnikovCommonRightCompositeSquare R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
