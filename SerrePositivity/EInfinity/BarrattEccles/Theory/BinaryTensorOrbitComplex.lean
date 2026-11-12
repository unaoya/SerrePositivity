module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorOrbitDecomposition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# 二色入力の軌道直和を複体全体で読む

HA 3.2.4.7 の自由比較のため、標準代表から誘導した入力の直和を
元の入力の複体に同定する。次数ごとの指定包含を変えずに、微分との可換性と
余極限性を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A) (r : ℕ)

/-- 各標準代表の入力を、微分を含めて安定化群から誘導する。 -/
def binaryTensorOrbitInducedComplex (k : ULift.{u} (Fin (r + 1))) :
    CochainComplex (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin r)))) ℤ :=
  ((Rep.indFunctor A (binaryTensorPatternSubgroup r k).subtype).mapHomologicalComplex
    (.up ℤ)).obj (binaryTensorOrbitInput X Y r k)

/-- 指定入力包含から誘導した、元の入力の複体への射。 -/
def binaryTensorOrbitInducedComplexInclusion (k : ULift.{u} (Fin (r + 1))) :
    binaryTensorOrbitInducedComplex X Y r k ⟶ binaryTensorFullInput X Y r :=
  finiteInductionCochainInclusion (binaryTensorPatternSubgroup r k)
    (binaryTensorOrbitInput X Y r k) (binaryTensorFullInput X Y r)
    (binaryTensorOrbitInputInclusion X Y r k)

/-- 各次数の包含も、既に固定した誘導表現の包含そのもの。 -/
lemma binaryTensorOrbitInducedComplexInclusion_f (k : ULift.{u} (Fin (r + 1))) (i : ℤ) :
    (binaryTensorOrbitInducedComplexInclusion X Y r k).f i =
      binaryTensorOrbitInducedInclusion X Y r k i := rfl

/-- 元の入力の複体を頂点とする、指定包含の余錐。 -/
def binaryTensorOrbitComplexCofan : Cofan (binaryTensorOrbitInducedComplex X Y r) :=
  Cofan.mk (binaryTensorFullInput X Y r) (binaryTensorOrbitInducedComplexInclusion X Y r)

/-- 次数ごとの実際の直和分解は、表現の複体の余極限を与える。 -/
def binaryTensorOrbitComplexIsColimit : IsColimit (binaryTensorOrbitComplexCofan X Y r) :=
  HomologicalComplex.isColimitOfEval _ _ fun i =>
    (isColimitMapCoconeCofanMkEquiv
      (HomologicalComplex.eval (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin r)))) (.up ℤ) i)
      (binaryTensorOrbitInducedComplex X Y r)
      (binaryTensorOrbitInducedComplexInclusion X Y r)).symm
      (binaryTensorOrbitBiconeIsBilimit X Y r i).isColimit

/-- 誘導入力の直和と元の入力は、複体として同型である。 -/
def binaryTensorOrbitComplexIso :
    (∐ binaryTensorOrbitInducedComplex X Y r) ≅ binaryTensorFullInput X Y r :=
  (coproductIsCoproduct (binaryTensorOrbitInducedComplex X Y r)).coconePointUniqueUpToIso
    (binaryTensorOrbitComplexIsColimit X Y r)

/-- 直和同型は、各生成元を指定された入力包含へ送る。 -/
lemma binaryTensorOrbitComplexIso_ι (k : ULift.{u} (Fin (r + 1))) :
    Sigma.ι (binaryTensorOrbitInducedComplex X Y r) k ≫
        (binaryTensorOrbitComplexIso X Y r).hom =
      binaryTensorOrbitInducedComplexInclusion X Y r k :=
  (coproductIsCoproduct (binaryTensorOrbitInducedComplex X Y r)).comp_coconePointUniqueUpToIso_hom
    (binaryTensorOrbitComplexIsColimit X Y r) (Discrete.mk k)

end SerrePositivity.EInfinity
