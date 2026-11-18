module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurArityTotalComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorOrbitTransport
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorInducedComplexInputs

/-!
# Schur 表示の係数と入力の順序の比較

HA 3.2.4.7 の自由比較で、Schur の係数優先の表示を誘導表現の入力優先の表示へ運ぶ。
braiding は元の複体の Koszul の符号を含むものを使い、係数も実際の arity の作用に同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A G : Type u} [CommRing A] [Group G] {K L : Complex A}

/-- 元の braiding は、対角作用を持つ表現の複体にも持ち上がる。 -/
def representationTensorBraidingIso (ρ : G →* End K) (σ : G →* End L) :
    representationCochainComplex (tensorComplexAction ρ σ) ≅
      representationCochainComplex (tensorComplexAction σ ρ) :=
  representationCochainIso (tensorComplexAction ρ σ) (tensorComplexAction σ ρ) (β_ K L)
    (fun g => BraidedCategory.braiding_naturality (ρ g).asHom (σ g).asHom)

/-- 余不変の全複体の左右の順序を、指定 braiding に沿って交換する。 -/
def coinvariantTensorTotalSwapIso (ρ : G →* End K) (σ : G →* End L) :
    coinvariantTensorTotal ρ σ ≅ coinvariantTensorTotal σ ρ :=
  coinvariantTensorTotalIso ρ σ ≪≫
    ((Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)).mapIso
      (representationTensorBraidingIso ρ σ) ≪≫ (coinvariantTensorTotalIso σ ρ).symm

/-- 元のテンソルから、指定商写像によりテンソル余不変の全複体へ送る。 -/
def coinvariantTotalQuotient (ρ : G →* End K) (σ : G →* End L) :
    K ⊗ L ⟶ coinvariantTensorTotal ρ σ :=
  (representationCochainForgetIso (tensorComplexAction ρ σ)).inv ≫
    (NatTrans.mapHomologicalComplex (Rep.coinvariantsMk A G) (.up ℤ)).app
      (representationCochainComplex (tensorComplexAction ρ σ)) ≫
        (coinvariantTensorTotalIso ρ σ).inv

/-- 指定商を全複体の比較で戻すと、元の余不変の商写像になる。 -/
lemma coinvariantTotalQuotient_comparison (ρ : G →* End K) (σ : G →* End L) :
    coinvariantTotalQuotient ρ σ ≫ (coinvariantTensorTotalIso ρ σ).hom =
      (representationCochainForgetIso (tensorComplexAction ρ σ)).inv ≫
        (NatTrans.mapHomologicalComplex (Rep.coinvariantsMk A G) (.up ℤ)).app
          (representationCochainComplex (tensorComplexAction ρ σ)) := by
  simp [coinvariantTotalQuotient, Category.assoc]

/-- 双次数の生成元で、指定全複体商は元のテンソル余不変の商そのものである。 -/
lemma coinvariantTotalQuotient_ι (ρ : G →* End K) (σ : G →* End L)
    (i j k : ℤ) (h : i + j = k) :
    ιTensorObj K L i j k h ≫ (coinvariantTotalQuotient ρ σ).f k =
      (Rep.coinvariantsMk A G).app (tensorDegreeRepresentationSummand ρ σ k ⟨(i, j), h⟩) ≫
        ιMapBifunctor (representationCochainComplex ρ) (representationCochainComplex σ)
          (Rep.coinvariantsTensor A G) (.up ℤ) i j k h := by
  apply (cancel_mono ((coinvariantTensorTotalIso ρ σ).hom.f k)).1
  rw [Category.assoc, ← HomologicalComplex.comp_f, coinvariantTotalQuotient_comparison,
    HomologicalComplex.comp_f]
  change ιTensorObj K L i j k h ≫ (Rep.coinvariantsMk A G).app
      (Rep.of (complexDegreeRepresentation (tensorComplexAction ρ σ) k)) =
    (Rep.coinvariantsMk A G).app (tensorDegreeRepresentationSummand ρ σ k ⟨(i, j), h⟩) ≫
      (ιMapBifunctor (representationCochainComplex ρ) (representationCochainComplex σ)
        (Rep.coinvariantsTensor A G) (.up ℤ) i j k h ≫ (tensorDegreeCoinvariantsIso ρ σ k).inv)
  rw [coinvariantTensorTotal_ι_inverse]
  exact (Rep.coinvariantsMk A G).naturality (tensorDegreeRepresentationLeg ρ σ k ⟨(i, j), h⟩)

/-- 指定商写像の下での順序交換は、元の複体の braiding そのもの。 -/
lemma coinvariantTotalQuotient_swap (ρ : G →* End K) (σ : G →* End L) :
    coinvariantTotalQuotient ρ σ ≫ (coinvariantTensorTotalSwapIso ρ σ).hom =
      (β_ K L).hom ≫ coinvariantTotalQuotient σ ρ := by
  simp only [coinvariantTotalQuotient, coinvariantTensorTotalSwapIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  rfl

namespace BarrattEccles
variable (A : Type u) [CommRing A]

/-- 実際の対称列の arity の作用は、係数比較で指定した作用そのもの。 -/
lemma sequenceComplexAction_eq (n : ℕ) :
    finiteBijectionComplexAction (sequence A) n = arityComplexAction A n := by
  apply MonoidHom.ext
  intro g
  apply End.ext
  exact sequence_map_permutation A n g.down

/-- 対称列で読む係数と、指定 arity の係数は、複体の同じ射を持つ。 -/
def sequenceArityRepresentationIso (n : ℕ) :
    representationCochainComplex (finiteBijectionComplexAction (sequence A) n) ≅
      arityRepresentationCochain A n :=
  eqToIso (congrArg representationCochainComplex (sequenceComplexAction_eq A n))

/-- 実際の Schur の一つの arity を、入力優先・指定係数の全複体へ運ぶ。 -/
def schurArityInputCoefficientIso (K : Complex A) (n : ℕ) :
    arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) K) n ≅
      (((Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin n)))).map₂CochainComplex).obj
        (representationCochainComplex (finiteBijectionComplexAction (bijectionFunctor K) n))).obj
          (arityRepresentationCochain A n) :=
  schurArityTotalIso (sequence A) K n ≪≫
    coinvariantTensorTotalSwapIso (finiteBijectionComplexAction (sequence A) n)
      (finiteBijectionComplexAction (bijectionFunctor K) n) ≪≫
    (((Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin n)))).map₂CochainComplex).obj
      (representationCochainComplex (finiteBijectionComplexAction (bijectionFunctor K) n))).mapIso
        (sequenceArityRepresentationIso A n)

/-- 和の入力において、対称列の入力作用は既存の実際の全入力の作用に一致する。 -/
def binaryTensorFullInputSequenceIso (X Y : Complex A) (r : ℕ) :
    representationCochainComplex (finiteBijectionComplexAction (bijectionFunctor (X ⊞ Y)) r) ≅
      binaryTensorFullInput X Y r := by
  apply eqToIso
  apply congrArg representationCochainComplex
  apply MonoidHom.ext
  intro g
  apply End.ext
  exact bijectionFunctor_map_permutation (X ⊞ Y) r g.down

end BarrattEccles
end SerrePositivity.EInfinity
