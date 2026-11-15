module

public import SerrePositivity.AlgebraicGeometry.CoefficientModelCategory
public import Mathlib.RingTheory.FiniteType

/-!
概要：全模型から実際の有限生成部分代数の模型へ移し、像による射の一致判定を供給する。
方針：両辺の像への全射から有限型性を得て、元の g の制限で正方形を作る。
規約：元の R,C の Noether 性を要求しない。
使われ方：B03・B04 の全模型の共同後段・平行射の一致・余極限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

/-- 有限型代数の像は実際の有限生成部分代数。 -/
theorem fg_algHom_range {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] (f : A →ₐ[k] B) : f.range.FG :=
  (Subalgebra.fg_iff_finiteType f.range).mpr
    (Algebra.FiniteType.of_surjective f.rangeRestrict f.rangeRestrict_surjective)

/-- g で両立する有限生成部分代数は、元の g への実際の模型を与える。 -/
def coefficientModelSubalgebraObj (A : Subalgebra k R) (D : Subalgebra k C)
    (hA : A.FG) (hD : D.FG) (hAD : A.map g ≤ D) : CoefficientModelCategory k g := by
  letI : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).mp hA
  letI : Algebra.FiniteType k D := (Subalgebra.fg_iff_finiteType D).mp hD
  let t : A →ₐ[k] D := (g.comp A.val).codRestrict D
    (fun x ↦ hAD ⟨x, x.property, rfl⟩)
  exact coefficientModelObj g t A.val D.val (by ext x; rfl)

/-- 両辺の像を含む有限生成部分代数へ、元の模型からの実際の射を作る。 -/
def coefficientModelToSubalgebraObj
    (A : Subalgebra k R) (D : Subalgebra k C) (hA : A.FG) (hD : D.FG) (hAD : A.map g ≤ D)
    (X : CoefficientModelCategory k g)
    (hAX : ∀ x, X.hom.left.hom x ∈ A) (hDX : ∀ x, X.hom.right.hom x ∈ D) :
    X ⟶ coefficientModelSubalgebraObj g A D hA hD hAD := by
  let a := X.hom.left.hom.codRestrict A hAX
  let d := X.hom.right.hom.codRestrict D hDX
  refine coefficientModelHomMk g a d ?_ ?_ ?_
  · apply AlgHom.ext
    intro x
    apply Subtype.ext
    exact (DFunLike.congr_fun (coefficientModel_comm g X) x).symm
  · apply AlgHom.ext
    intro x
    rfl
  · apply AlgHom.ext
    intro x
    rfl

/-- 元の二環への構造射が単射な標的への模型の射は一意。 -/
theorem coefficientModelHom_eq_of_injective_target
    {X Y : CoefficientModelCategory k g}
    (ha : Function.Injective Y.hom.left.hom) (hd : Function.Injective Y.hom.right.hom)
    (f h : X ⟶ Y) : f = h := by
  apply coefficientModelHom_ext g
  · apply AlgHom.ext
    intro x
    apply ha
    exact DFunLike.congr_fun ((coefficientModelHom_base_triangle g f).trans
      (coefficientModelHom_base_triangle g h).symm) x
  · apply AlgHom.ext
    intro x
    apply hd
    exact DFunLike.congr_fun ((coefficientModelHom_source_triangle g f).trans
      (coefficientModelHom_source_triangle g h).symm) x

/-- 任意の全模型を、元の二環の実際の像の模型へ移す。 -/
def coefficientModelImageObj (X : CoefficientModelCategory k g) : CoefficientModelCategory k g :=
  coefficientModelSubalgebraObj g X.hom.left.hom.range X.hom.right.hom.range
    (fg_algHom_range (A := X.left.left.obj) X.hom.left.hom) (fg_algHom_range (A := X.left.right.obj) X.hom.right.hom) (by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := hx
      exact ⟨X.left.hom.hom.hom z, DFunLike.congr_fun (coefficientModel_comm g X) z⟩)

/-- 任意の全模型から、その実際の像の模型への射。 -/
def coefficientModelToImage (X : CoefficientModelCategory k g) : X ⟶ coefficientModelImageObj g X := by
  dsimp only [coefficientModelImageObj]
  apply coefficientModelToSubalgebraObj
  · intro x
    exact AlgHom.mem_range_self _ x
  · intro x
    exact AlgHom.mem_range_self _ x

/-- 像の模型の基底側の構造射は単射。 -/
theorem coefficientModelImage_base_injective (X : CoefficientModelCategory k g) :
    Function.Injective (coefficientModelImageObj g X).hom.left.hom :=
  Subtype.val_injective

/-- 像の模型の始域側の構造射は単射。 -/
theorem coefficientModelImage_source_injective (X : CoefficientModelCategory k g) :
    Function.Injective (coefficientModelImageObj g X).hom.right.hom :=
  Subtype.val_injective

end SerrePositivity.AlgebraicGeometry
