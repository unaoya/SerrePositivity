module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeHopfComparison
public import SerrePositivity.EInfinity.Operad.FreeAlgebraAdjunction
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# 自由代数の指定余積と Hopf 比較

HA 3.2.4.7。自由関手の標準余積比較を使い、自由生成元で定めた Hopf 射を
厳密な余積の指定射へ戻す。係数比較との一致や擬同型性は別に証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
attribute [local implicit_reducible] Operad.freeAlgebraFunctor
variable {A : Type u} [CommRing A] {P : Operad A}
  [HasBinaryCoproducts P.Algebra] (X Y : Complex A)

/-- 自由関手の標準余積比較を、同じ二項直和に正規化する。 -/
def freeSumCoproductIso : P.freeAlgebra X ⨿ P.freeAlgebra Y ≅ P.freeAlgebra (X ⊞ Y) := by
  letI := P.freeAlgebraAdjunction.isLeftAdjoint
  exact asIso (coprodComparison P.freeAlgebraFunctor X Y) ≪≫
    P.freeAlgebraFunctor.mapIso (biprod.isoCoprod X Y).symm

/-- 正規化した同型は第一の指定包含を自由生成元の包含へ送る。 -/
@[reassoc]
lemma freeSumCoproductIso_inl :
    coprod.inl ≫ (freeSumCoproductIso (P := P) X Y).hom =
      P.freeAlgebraFunctor.map biprod.inl := by
  simp only [freeSumCoproductIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Iso.symm_hom, biprod.isoCoprod_inv]
  rw [← Category.assoc]
  erw [coprodComparison_inl P.freeAlgebraFunctor (A := X) (B := Y)]
  rw [← Functor.map_comp, coprod.inl_desc]

/-- 正規化した同型は第二の指定包含を自由生成元の包含へ送る。 -/
@[reassoc]
lemma freeSumCoproductIso_inr :
    coprod.inr ≫ (freeSumCoproductIso (P := P) X Y).hom =
      P.freeAlgebraFunctor.map biprod.inr := by
  simp only [freeSumCoproductIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Iso.symm_hom, biprod.isoCoprod_inv]
  rw [← Category.assoc]
  erw [coprodComparison_inr P.freeAlgebraFunctor (A := X) (B := Y)]
  rw [← Functor.map_comp, coprod.inr_desc]

/-- 自由生成元で定めた射は、元の厳密な余積の同じ Hopf 比較である。 -/
lemma freeSumCoproductIso_hopfComparison (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0))) :
    (freeSumCoproductIso (P := P) X Y).hom ≫ freeHopfComparison hP h0 X Y =
      hopfCoproductComparison hP h0 (P.freeAlgebra X) (P.freeAlgebra Y) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, freeSumCoproductIso_inl,
      hopfCoproductComparison, coprod.inl_desc]
    apply Operad.Algebra.freeAlgebraHom_ext
    change P.schurUnit X ≫ (schurFunctor A P.sequence).map biprod.inl ≫
      (freeHopfComparison hP h0 X Y).hom = _
    rw [← P.schurUnit_naturality_assoc]
    exact freeHopfComparison_left hP h0 X Y
  · rw [← Category.assoc, freeSumCoproductIso_inr,
      hopfCoproductComparison, coprod.inr_desc]
    apply Operad.Algebra.freeAlgebraHom_ext
    change P.schurUnit Y ≫ (schurFunctor A P.sequence).map biprod.inr ≫
      (freeHopfComparison hP h0 X Y).hom = _
    rw [← P.schurUnit_naturality_assoc]
    exact freeHopfComparison_right hP h0 X Y

/-- 自由生成元での指定射の擬同型性を、元の厳密な余積比較へ移す。 -/
lemma hopfCoproductComparison_quasiIso_of_free (hP : P.Hopf)
    (h0 : IsIso (hP.counit.map.app (FiniteBijection.of 0)))
    [QuasiIso (freeHopfComparison hP h0 X Y).hom] :
    QuasiIso
      (hopfCoproductComparison hP h0 (P.freeAlgebra X) (P.freeAlgebra Y)).hom := by
  have hi : IsIso (freeSumCoproductIso (P := P) X Y).hom.hom :=
    inferInstanceAs (IsIso ((Operad.Algebra.forget P).map
      (freeSumCoproductIso (P := P) X Y).hom))
  have he := congrArg Operad.AlgebraHom.hom
    (freeSumCoproductIso_hopfComparison X Y hP h0)
  change (freeSumCoproductIso (P := P) X Y).hom.hom ≫
    (freeHopfComparison hP h0 X Y).hom = _ at he
  rw [← he]
  infer_instance

end SerrePositivity.EInfinity
