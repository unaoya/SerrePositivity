module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCode
/-!
概要：係数閉包の固定基底コードの評価は、全 Hom 複体で単射である。
方針：商による提示と係数 span の同型の後に、元の Hom への単射を合成する。
規約：対象ラベルの重複を許し、充満性を仮定しない。
使われ方：c′ の出発関手と閉射の係数精密化の等式を実 dg 圏で反映する。
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

lemma codeEvaluation_homMono
    (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ) :
    Mono ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y) := by
  let e : homObject R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y ≅
      homComplex source target degree R D value coefficient x y := by
    letI := category source target degree R D value coefficient
    exact dgCategoryHomSurjectionIso R (Set.Iio a) κ a id
      (ordinalCover R D κ a source target degree value coefficient hκ hI)
      (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI) x y
  change Mono (e.hom ≫ inclusion source target degree R D value coefficient x y)
  infer_instance

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
