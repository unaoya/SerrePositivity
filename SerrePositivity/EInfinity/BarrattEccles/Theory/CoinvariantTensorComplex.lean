module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# テンソル余不変と直和全複体の比較

HA 3.2.4.7 の自由比較で、複体のテンソルの余不変を、表現の複体の
テンソル余不変の全複体に同定する。両方の微分と指定された双次数包含を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A G : Type u} [CommRing A] [Group G] {K L : CochainComplex (ModuleCat.{u} A) ℤ}
  (ρ : G →* End K) (σ : G →* End L)

/-- 実際のテンソル複体の対角作用の余不変。 -/
def tensorCoinvariantComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((Rep.coinvariantsFunctor A G).mapHomologicalComplex (.up ℤ)).obj
    (representationCochainComplex (tensorComplexAction ρ σ))

/-- 入力と係数それぞれの微分を持つ、テンソル余不変の直和全複体。 -/
abbrev coinvariantTensorTotal : CochainComplex (ModuleCat.{u} A) ℤ :=
  mapBifunctor (representationCochainComplex ρ) (representationCochainComplex σ)
    (Rep.coinvariantsTensor A G) (.up ℤ)

/-- 双次数の指定包含を保持する、次数ごとの比較。 -/
lemma coinvariantTensorTotal_ι_inverse (i j k : ℤ) (h : i + j = k) :
    ιMapBifunctor (representationCochainComplex ρ) (representationCochainComplex σ)
        (Rep.coinvariantsTensor A G) (.up ℤ) i j k h ≫
          (tensorDegreeCoinvariantsIso ρ σ k).inv =
      (Rep.coinvariantsFunctor A G).map
        (tensorDegreeRepresentationLeg ρ σ k ⟨(i, j), h⟩) := by
  exact (isColimitCofanMkObjOfIsColimit (Rep.coinvariantsFunctor A G)
    (tensorDegreeRepresentationSummand ρ σ k) (tensorDegreeRepresentationLeg ρ σ k)
    (tensorDegreeRepresentationIsColimit ρ σ k)).comp_coconePointUniqueUpToIso_inv
      (colimit.isColimit (Discrete.functor _)) (Discrete.mk ⟨(i, j), h⟩)

/-- 表現の圏でも、指定双次数包含は元のテンソル微分の符号公式を満たす。 -/
lemma tensorDegreeRepresentationLeg_d (i j k : ℤ) (h : i + j = k) :
    tensorDegreeRepresentationLeg ρ σ k ⟨(i, j), h⟩ ≫
        (representationCochainComplex (tensorComplexAction ρ σ)).d k (k + 1) =
      ((representationCochainComplex ρ).d i (i + 1) ▷
          (representationCochainComplex σ).X j) ≫
        tensorDegreeRepresentationLeg ρ σ (k + 1) ⟨(i + 1, j), by omega⟩ +
      i.negOnePow • (((representationCochainComplex ρ).X i ◁
          (representationCochainComplex σ).d j (j + 1)) ≫
        tensorDegreeRepresentationLeg ρ σ (k + 1) ⟨(i, j + 1), by omega⟩) := by
  apply (forget₂ (Rep.{u} A G) (ModuleCat A)).map_injective
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_add,
    CategoryTheory.Functor.map_units_smul]
  apply ModuleCat.hom_ext
  exact congrArg ModuleCat.Hom.hom (SerrePositivity.ιTensorObj_cochainTensor_d K L i j k h)

/-- 各次数の比較は、両入力の微分を保つ複体の射になる。 -/
def coinvariantTensorTotalComparison :
    coinvariantTensorTotal ρ σ ⟶ tensorCoinvariantComplex ρ σ where
  f k := (tensorDegreeCoinvariantsIso ρ σ k).inv
  comm' k l hkl := by
    change k + 1 = l at hkl
    subst l
    apply mapBifunctor.hom_ext
    intro i j h
    change i + j = k at h
    rw [← Category.assoc, coinvariantTensorTotal_ι_inverse]
    dsimp only [tensorCoinvariantComplex, CategoryTheory.Functor.mapHomologicalComplex_obj_d]
    rw [← CategoryTheory.Functor.map_comp, tensorDegreeRepresentationLeg_d]
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_units_smul,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
      mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc,
      mapBifunctor.d₁_eq _ _ _ _ rfl _ _ (by dsimp; omega),
      mapBifunctor.d₂_eq _ _ _ _ _ rfl _ (by dsimp; omega)]
    simp [Category.assoc, coinvariantTensorTotal_ι_inverse]

/-- 各次数で同型なので、指定比較は複体そのものの同型である。 -/
instance : IsIso (coinvariantTensorTotalComparison ρ σ) := by
  have (i : ℤ) : IsIso ((coinvariantTensorTotalComparison ρ σ).f i) := by
    change IsIso (tensorDegreeCoinvariantsIso ρ σ i).inv
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 微分と双次数包含を保つ、テンソル余不変の全複体との指定同型。 -/
def coinvariantTensorTotalIso :
    coinvariantTensorTotal ρ σ ≅ tensorCoinvariantComplex ρ σ :=
  asIso (coinvariantTensorTotalComparison ρ σ)

/-- 同型の順射は既に指定した比較である。 -/
lemma coinvariantTensorTotalIso_hom :
    (coinvariantTensorTotalIso ρ σ).hom = coinvariantTensorTotalComparison ρ σ := rfl

end SerrePositivity.EInfinity
