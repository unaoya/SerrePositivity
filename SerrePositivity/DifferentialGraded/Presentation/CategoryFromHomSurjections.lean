module
public import SerrePositivity.DifferentialGraded.Presentation.CategoryCode
public import SerrePositivity.DifferentialGraded.Presentation.ComplexFromSurjections
public import SerrePositivity.DifferentialGraded.Category.HomTransport
public import SerrePositivity.DifferentialGraded.Category.Induced
public import SerrePositivity.DifferentialGraded.Functor.Basic
/-!
概要：固定自由加群で被覆された Hom 複体を持つ小対象族を、dg 圏の提示コードへ戻す。
方針：各次数の商の同型で Hom を符号化し、元の dg 単位・合成・三法則を移送する。
規約：Hom の生成元被覆を明示入力とし、係数閉包の小ささを仮定なく結論しない。
使われ方：c′ の共通源係数精密化を固定基底の提示模型へ符号化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (value : Set.Iio a → D)
  (q : ∀ x y : Set.Iio a, ∀ n : ℤ,
    (κ.ord.ToType →₀ R) →ₗ[R] (homObject R D (value x) (value y)).X n)
  (hq : ∀ x y n, Function.Surjective (q x y n))

abbrev dgCategoryHomSurjectionCode (x y : Set.Iio a) :
    DGComplexPresentationCode R κ.ord.ToType :=
  DGComplexPresentationCode.ofSurjections R κ.ord.ToType
    (homObject R D (value x) (value y)) (q x y) (hq x y)

def dgCategoryHomSurjectionIso (x y : Set.Iio a) :
    (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType ≅
      homObject R D (value x) (value y) :=
  DGComplexPresentationCode.ofSurjectionsIso R κ.ord.ToType
    (homObject R D (value x) (value y)) (q x y) (hq x y)

def dgCategoryPresentationOfHomSurjections : DGCategoryPresentationCode R κ where
  ordinal := a
  hom := dgCategoryHomSurjectionCode R D κ a value q hq
  unit x := eId (Complex R) (value x) ≫ (dgCategoryHomSurjectionIso R D κ a value q hq x x).inv
  comp x y z :=
    ((dgCategoryHomSurjectionIso R D κ a value q hq x y).hom ⊗ₘ
      (dgCategoryHomSurjectionIso R D κ a value q hq y z).hom) ≫
    eComp (Complex R) (value x) (value y) (value z) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x z).inv
  left := by
    letI := inducedDGCategory R value
    exact dgHomTransport_left R (Set.Iio a)
      (fun x y => (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType)
      (dgCategoryHomSurjectionIso R D κ a value q hq)
  right := by
    letI := inducedDGCategory R value
    exact dgHomTransport_right R (Set.Iio a)
      (fun x y => (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType)
      (dgCategoryHomSurjectionIso R D κ a value q hq)
  assoc := by
    letI := inducedDGCategory R value
    exact dgHomTransport_assoc R (Set.Iio a)
      (fun x y => (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType)
      (dgCategoryHomSurjectionIso R D κ a value q hq)

def dgCategoryPresentationOfHomSurjectionsEvaluation :
    DGFunctor R ((dgCategoryPresentationOfHomSurjections R D κ a value q hq).Objects R κ) D where
  obj := value
  map x y := (dgCategoryHomSurjectionIso R D κ a value q hq x y).hom
  map_id x := by
    change (eId (Complex R) (value x) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x x).inv) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x x).hom = _
    simp
  map_comp x y z := by
    change (((dgCategoryHomSurjectionIso R D κ a value q hq x y).hom ⊗ₘ
      (dgCategoryHomSurjectionIso R D κ a value q hq y z).hom) ≫
      eComp (Complex R) (value x) (value y) (value z) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x z).inv) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x z).hom = _
    simp

lemma dgCategoryPresentationOfHomSurjectionsEvaluation_homIso
    (x y : (dgCategoryPresentationOfHomSurjections R D κ a value q hq).Objects R κ) :
    IsIso ((dgCategoryPresentationOfHomSurjectionsEvaluation R D κ a value q hq).map x y) := by
  change IsIso (dgCategoryHomSurjectionIso R D κ a value q hq x y).hom
  infer_instance

end SerrePositivity.DifferentialGraded
