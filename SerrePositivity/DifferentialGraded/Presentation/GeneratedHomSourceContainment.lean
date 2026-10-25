module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomFunctorLift
public import SerrePositivity.DifferentialGraded.Presentation.CategoryCode
public import SerrePositivity.DifferentialGraded.Presentation.QuotientGeneratorImage
/-!
概要：元の出発提示の各 Hom の全像は、固定基底の像を含めるだけで係数閉包に入る。
方針：提示の商による Hom をその固定自由基底へ戻し、線形像の span 帰納を使う。
規約：元の dg 関手と関係部分加群を保持し、関係の個数を制限しない。
使われ方：c′ の元の二つの出発圏を共通係数閉包へ含めるための全 Hom 判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)

def dgCodeHomGenerator (x y : c.Objects R κ) (n : ℤ) (b : κ.ord.ToType) : GradedHom R x y n :=
  ((c.hom x y).relations n).mkQ (Finsupp.single b 1)

variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))

lemma generatedHomImage_of_codeGenerators
    (hgen : ∀ x y n b, (F.map x y).f n (dgCodeHomGenerator R κ c x y n b) ∈
      DGGeneratedHomWord.linearSpan source target degree R D value coefficient
        (F.obj x).label (F.obj y).label n) :
    ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
      DGGeneratedHomWord.linearSpan source target degree R D value coefficient
        (F.obj x).label (F.obj y).label n := by
  intro x y n f
  exact quotientGeneratorImage_mem ((c.hom x y).relations n) ((F.map x y).f n).hom
    (DGGeneratedHomWord.linearSpan source target degree R D value coefficient
      (F.obj x).label (F.obj y).label n) (hgen x y n) f

end SerrePositivity.DifferentialGraded
