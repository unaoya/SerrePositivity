module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCategory
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomFreeCover
public import SerrePositivity.DifferentialGraded.Presentation.CategoryFromHomSurjections
/-!
概要：κ 個以下の指定係数の dg 閉包を既存の小出発提示コードへ符号化する。
方針：閉包の各 Hom に固定自由被覆を選び、全 Hom 同型を保つ提示と実評価を合成する。
規約：出発対象の ordinal ラベルと元の実 Hom への単射性を保持する。
使われ方：c′ の任意閉射を含む係数精密化で使う共通出発コードの構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord

include hκ hI in
lemma fixedFreeCover_ordinal (x y : Set.Iio a) (n : ℤ) :
    ∃ q : (κ.ord.ToType →₀ R) →ₗ[R]
      linearSpan source target degree R D value coefficient x y n, Function.Surjective q :=
  fixedFreeCover_exists source target degree R D value coefficient κ hκ hI
    (le_of_lt (by simpa using Cardinal.mk_Iio_lt a (by simp))) x y n

def ordinalCover (x y : Set.Iio a) (n : ℤ) :
    (κ.ord.ToType →₀ R) →ₗ[R] linearSpan source target degree R D value coefficient x y n :=
  (fixedFreeCover_ordinal R D κ a source target degree value coefficient hκ hI x y n).choose

lemma ordinalCover_surjective (x y : Set.Iio a) (n : ℤ) :
    Function.Surjective (ordinalCover R D κ a source target degree value coefficient hκ hI x y n) :=
  (fixedFreeCover_ordinal R D κ a source target degree value coefficient hκ hI x y n).choose_spec

def code : DGCategoryPresentationCode R κ := by
  letI := category source target degree R D value coefficient
  exact dgCategoryPresentationOfHomSurjections R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI)

def codeEvaluation : DGFunctor R
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) D := by
  letI := category source target degree R D value coefficient
  exact (dgCategoryPresentationOfHomSurjectionsEvaluation R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI)).comp
      (evaluation source target degree R D value coefficient)

lemma codeEvaluation_obj
    (x : (code R D κ a source target degree value coefficient hκ hI).Objects R κ) :
    (codeEvaluation R D κ a source target degree value coefficient hκ hI).obj x = value x := rfl

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
