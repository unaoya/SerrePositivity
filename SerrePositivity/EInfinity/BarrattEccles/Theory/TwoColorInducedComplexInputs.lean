module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorInducedCoefficients
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorComplexInputs

/-!
# 誘導入力の二色係数比較を任意の複体へ延ばす

HA 3.2.4.7 の自由比較で使う誘導表現の同型を、入力の微分にも自然な形で
二重複体へ持ち上げる。直和全複体へ移すので、入力の有界性・平坦性は仮定しない。
係数射は既存の指定された Hopf 比較のままとする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex

/-- 誘導表現とテンソル余不変の指定同型は、入力表現の射にも自然である。 -/
lemma coinvariantsTensorIndIso_naturality_left
    {A G H : Type u} [CommRing A] [Group G] [Group H] (φ : G →* H)
    {V W : Rep.{u} A G} (f : V ⟶ W) (B : Rep.{u} A H) :
    ((Rep.coinvariantsTensor A H).map ((Rep.indFunctor A φ).map f)).app B ≫
        (Rep.coinvariantsTensorIndIso φ W B).hom =
      (Rep.coinvariantsTensorIndIso φ V B).hom ≫
        ((Rep.coinvariantsTensor A G).map f).app (Rep.res φ B) := by
  apply ModuleCat.hom_ext
  apply Representation.Coinvariants.hom_ext
  apply TensorProduct.ext
  apply Representation.IndV.hom_ext
  intro h
  ext x y
  simp [Rep.coinvariantsTensorIndHom, Rep.coinvariantsTensorMk, Rep.indMap]

namespace BarrattEccles
variable (A : Type u) [CommRing A] (m n : ℕ)

/-- 任意の入力複体を、実際の対称群へ各次数で誘導する。 -/
abbrev twoColorInducedInput
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :=
  ((Rep.indFunctor A
    (twoColorPermutationHom.{u} m n).range.subtype).mapHomologicalComplex (.up ℤ)).obj V

/-- 係数複体を保持した誘導入力の比較は、入力複体の微分と可換。 -/
def twoColorInducedSourceBicomplexIso
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :
    (((Rep.coinvariantsTensor A
      (ULift.{u} (Equiv.Perm (Fin (m + n))))).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
          (twoColorInducedInput A m n V)).obj (arityRepresentationCochain A (m + n)) ≅
      (((Rep.coinvariantsTensor A
        (TwoColorGroup.{u} m n)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj V).obj
          (twoColorSourceCochain A m n) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => twoColorInducedSourceIso A m n (V.X i)) (by
      intro i j hij
      apply HomologicalComplex.Hom.ext
      funext k
      let φ := (twoColorPermutationHom.{u} m n).range.subtype
      let B := (arityRepresentationCochain A (m + n)).X k
      let t := (twoColorSourceRestrictionIso A m n).hom.f k
      have hr (a : ℤ) : (twoColorInducedSourceIso A m n (V.X a)).hom.f k =
          (Rep.coinvariantsTensorIndIso φ (V.X a) B).hom ≫
            ((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj (V.X a)).map t := by
        simp [twoColorInducedSourceIso, φ, B, t]
      change (twoColorInducedSourceIso A m n (V.X i)).hom.f k ≫
          ((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).map (V.d i j)).app
            ((twoColorSourceCochain A m n).X k) =
        ((Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin (m + n))))).map
          ((Rep.indFunctor A φ).map (V.d i j))).app B ≫
            (twoColorInducedSourceIso A m n (V.X j)).hom.f k
      rw [hr i, hr j, Category.assoc,
        ((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).map (V.d i j)).naturality t,
        ← Category.assoc]
      simpa only [Category.assoc, CategoryTheory.Functor.mapHomologicalComplex_obj_X,
        twoColorInducedInput, CategoryTheory.Functor.comp_obj] using congrArg
        (fun f => f ≫ ((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj (V.X j)).map t)
        (coinvariantsTensorIndIso_naturality_left φ (V.d i j) B).symm)

/-- 誘導入力の比較は、任意の入力複体の直和全複体の同型になる。 -/
def twoColorInducedComplexSourceIso
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :
    mapBifunctor (twoColorInducedInput A m n V) (arityRepresentationCochain A (m + n))
      (Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin (m + n))))) (.up ℤ) ≅
      ((twoColorInputTotalFunctor A m n).obj V).obj (twoColorSourceCochain A m n) :=
  HomologicalComplex₂.total.mapIso (twoColorInducedSourceBicomplexIso A m n V) (.up ℤ)

/-- 任意の入力複体で、指定二色係数射は誘導表示からの鎖ホモトピー同値を与える。 -/
def twoColorInducedComplexCoefficientHomotopyEquiv
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :=
  (HomotopyEquiv.ofIso (twoColorInducedComplexSourceIso A m n V)).trans
    (twoColorComplexInputHomotopyEquiv A m n V)

/-- 得られた比較の順射は、指定同型の後の元の係数射である。 -/
lemma twoColorInducedComplexCoefficientHomotopyEquiv_hom
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :
    (twoColorInducedComplexCoefficientHomotopyEquiv A m n V).hom =
      (twoColorInducedComplexSourceIso A m n V).hom ≫
        ((twoColorInputTotalFunctor A m n).obj V).map (twoColorCoefficientCochainMap A m n) := rfl

end BarrattEccles
end SerrePositivity.EInfinity
