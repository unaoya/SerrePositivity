module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorInducedComplexInputs
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# 誘導入力の余不変の全複体と有限直和

HA 3.2.4.7 の自由比較の軌道直和を、任意の安定化群で扱うための補助。
指定した誘導表現の比較を微分と全複体へ延ばし、入力の有限直和との可換性を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex Limits
variable {A G H : Type u} [CommRing A] [Group G] [Group H]

/-- 誘導入力の余不変と制限した係数の比較は、任意の係数複体でも自然である。 -/
def inducedCoinvariantRowIso (φ : G →* H) (V : Rep.{u} A G)
    (B : CochainComplex (Rep.{u} A H) ℤ) :
    (((Rep.coinvariantsTensor A H).obj (Rep.ind φ V)).mapHomologicalComplex (.up ℤ)).obj B ≅
      (((Rep.coinvariantsTensor A G).obj V).mapHomologicalComplex (.up ℤ)).obj
        (((Rep.resFunctor φ).mapHomologicalComplex (.up ℤ)).obj B) :=
  (NatIso.mapHomologicalComplex (Rep.coinvariantsTensorIndNatIso φ V) (.up ℤ)).app B ≪≫
    ((Functor.mapHomologicalComplexCompIso (F := Rep.resFunctor φ)
      (G := (Rep.coinvariantsTensor A G).obj V) (Iso.refl _) (.up ℤ)).app B).symm

/-- 安定化群からの誘導と余不変の比較は、両方の微分を保つ。 -/
def inducedCoinvariantBicomplexIso (φ : G →* H)
    (V : CochainComplex (Rep.{u} A G) ℤ) (B : CochainComplex (Rep.{u} A H) ℤ) :
    (((Rep.coinvariantsTensor A H).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (((Rep.indFunctor A φ).mapHomologicalComplex (.up ℤ)).obj V)).obj B ≅
    (((Rep.coinvariantsTensor A G).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj V).obj
      (((Rep.resFunctor φ).mapHomologicalComplex (.up ℤ)).obj B) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => inducedCoinvariantRowIso φ (V.X i) B) (by
    intro i j hij
    apply HomologicalComplex.Hom.ext
    funext k
    simpa [inducedCoinvariantRowIso, Functor.mapHomologicalComplex_obj_X] using
      (coinvariantsTensorIndIso_naturality_left φ (V.d i j) (B.X k)).symm)

/-- 指定された誘導表示の比較を、任意の入力・係数の直和全複体へ移す。 -/
def inducedCoinvariantTotalIso (φ : G →* H)
    (V : CochainComplex (Rep.{u} A G) ℤ) (B : CochainComplex (Rep.{u} A H) ℤ) :
    mapBifunctor (((Rep.indFunctor A φ).mapHomologicalComplex (.up ℤ)).obj V) B
        (Rep.coinvariantsTensor A H) (.up ℤ) ≅
      mapBifunctor V (((Rep.resFunctor φ).mapHomologicalComplex (.up ℤ)).obj B)
        (Rep.coinvariantsTensor A G) (.up ℤ) :=
  HomologicalComplex₂.total.mapIso (inducedCoinvariantBicomplexIso φ V B) (.up ℤ)

/-- 係数を固定したテンソル余不変の全複体の関手。 -/
abbrev inputCoinvariantTotalFunctor (B : CochainComplex (Rep.{u} A G) ℤ) :=
  (Rep.coinvariantsTensor A G).map₂CochainComplex.flip.obj B

/-- 全複体の入力方向の関手は加法的であり、従って有限直和を保つ。 -/
instance inputCoinvariantTotalFunctor_additive (B : CochainComplex (Rep.{u} A G) ℤ) :
    (inputCoinvariantTotalFunctor B).Additive where
  map_add := by
    intro V W f g
    apply HomologicalComplex.Hom.ext
    funext k
    apply mapBifunctor.hom_ext
    intro i j h
    simp [inputCoinvariantTotalFunctor, ι_mapBifunctorMap, Preadditive.comp_add,
      CategoryTheory.Functor.map_add]

/-- 指定入力の有限直和を、元の直和包含を保って全複体の外へ移す。 -/
def inputCoinvariantTotalCoproductIso {J : Type u} [Finite J]
    (V : J → CochainComplex (Rep.{u} A G) ℤ) (B : CochainComplex (Rep.{u} A G) ℤ) :
    (inputCoinvariantTotalFunctor B).obj (∐ V) ≅
      ∐ (fun j => (inputCoinvariantTotalFunctor B).obj (V j)) :=
  PreservesCoproduct.iso (inputCoinvariantTotalFunctor B) V

end SerrePositivity.EInfinity
