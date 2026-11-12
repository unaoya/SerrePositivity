module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorInclusions
public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeSchurComparison

/-!
# 自由入力での指定 Hopf 比較

HA 3.2.4.7 の自由比較を、左右の指定包含により定める。
Schur の arity の生成射上の式を固定し、二色係数の全複体の比較との照合の入口にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {P : Operad A}
  (hP : P.Hopf) (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) (X Y : Complex A)

/-- 左右の自由生成元を、指定 Hopf 包含へ送る入力の射。 -/
def freeHopfComparisonInput :
    X ⊞ Y ⟶ (hopfTensorAlgebra hP (P.freeAlgebra X) (P.freeAlgebra Y)).carrier :=
  biprod.desc (P.schurUnit X ≫ (hopfTensorInl hP h0 (P.freeAlgebra X) (P.freeAlgebra Y)).hom)
    (P.schurUnit Y ≫ (hopfTensorInr hP h0 (P.freeAlgebra X) (P.freeAlgebra Y)).hom)

/-- 自由代数の指定比較は、左右の指定生成元からの唯一の代数射である。 -/
def freeHopfComparison :
    P.freeAlgebra (X ⊞ Y) ⟶ hopfTensorAlgebra hP (P.freeAlgebra X) (P.freeAlgebra Y) :=
  Operad.Algebra.liftHom _ (freeHopfComparisonInput hP h0 X Y)

/-- 自由比較は左の生成元を指定された Hopf 包含へ送る。 -/
lemma freeHopfComparison_left :
    biprod.inl ≫ P.schurUnit (X ⊞ Y) ≫ (freeHopfComparison hP h0 X Y).hom =
      P.schurUnit X ≫ (hopfTensorInl hP h0 (P.freeAlgebra X) (P.freeAlgebra Y)).hom := by
  rw [show P.schurUnit (X ⊞ Y) ≫ (freeHopfComparison hP h0 X Y).hom =
    freeHopfComparisonInput hP h0 X Y from Operad.Algebra.schurUnit_liftHom _ _]
  exact biprod.inl_desc _ _

/-- 自由比較は右の生成元を指定された Hopf 包含へ送る。 -/
lemma freeHopfComparison_right :
    biprod.inr ≫ P.schurUnit (X ⊞ Y) ≫ (freeHopfComparison hP h0 X Y).hom =
      P.schurUnit Y ≫ (hopfTensorInr hP h0 (P.freeAlgebra X) (P.freeAlgebra Y)).hom := by
  rw [show P.schurUnit (X ⊞ Y) ≫ (freeHopfComparison hP h0 X Y).hom =
    freeHopfComparisonInput hP h0 X Y from Operad.Algebra.schurUnit_liftHom _ _]
  exact biprod.inr_desc _ _

/-- 元の Schur arity の指定生成射上で、比較は指定入力のテンソル冪への作用である。 -/
lemma freeHopfComparison_arity (r : ℕ) :
    schurι A P.sequence (X ⊞ Y) r ≫ (freeHopfComparison hP h0 X Y).hom =
      (P.arity r ◁ TensorPowers.map (freeHopfComparisonInput hP h0 X Y) r) ≫
        (hopfTensorAlgebra hP (P.freeAlgebra X) (P.freeAlgebra Y)).action r := by
  rw [Operad.Algebra.freeAlgebraHom_ι]
  congr 3
  exact Operad.Algebra.schurUnit_liftHom _ _

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 単位入力の有限族を分離して縮約すると、各係数の右単位子になる。 -/
lemma tensorFamilyTensorIso_unit_right (n : ℕ) (V : Fin n → Complex A) :
    (tensorFamilyTensorIso n V (fun _ => 𝟙_ (Complex A))).hom ≫
      (𝟙 (tensorFamily n V) ⊗ₘ (tensorUnitFamilyIso A n).hom) ≫
      (ρ_ (tensorFamily n V)).hom = tensorFamilyMap n (fun j => (ρ_ (V j)).hom) := by
  induction n with
  | zero =>
    simp only [tensorFamilyTensorIso, tensorUnitFamilyIso, tensorFamily,
      tensorFamilyMap, Iso.symm_hom, Iso.refl_hom, tensorHom_id,
      id_whiskerRight, Category.id_comp]
    monoidal
  | succ n ih =>
    rw [tensorFamilyTensorIso, tensorUnitFamilyIso_succ_head]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, id_tensorHom,
      whiskerLeft_comp, Category.assoc]
    dsimp only [tensorFamily]
    have hn := tensorμ_natural_right (V 0) (𝟙_ (Complex A))
      (𝟙 (tensorFamily n (fun j => V j.succ))) (tensorUnitFamilyIso A n).hom
    simp only [whiskerLeft_id, id_tensorHom] at hn
    rw [← reassoc_of% hn, tensorUnitRightAssembly]
    rw [tensorHom_def']
    simp only [← whiskerLeft_comp_assoc]
    have hi := ih (fun j => V j.succ)
    simp only [id_tensorHom] at hi
    rw [hi]
    simp only [tensorFamilyMap, tensorHom_def']

end SerrePositivity.EInfinity
