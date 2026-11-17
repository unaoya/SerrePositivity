module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel

/-!
# 元の基底環上の affine 剰余模型と完備係数変更

## 概要
元の affine 剰余模型を prism の基底環上の余単体的加群として取り出す。

## 方針
元の基底脚を商に降ろし、各項の導来 p 完備性と既存の標準の完備係数変更を使う。

## 規約
完備多項式係数への作用の代わりに、同じ模型の元の基底環の作用を明示する。

## 使われ方
特定の Zp 係数射へ Lemma 4.22 を適用するときの、元の基底上の行模型。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 同じ affine 剰余模型の元の基底環からの構造射。 -/
def affineBaseCoefficients :
    (Functor.const SimplexCategory).obj (CommRingCat.of A) ⟶ reducedModel P hP r :=
  htBase P hP r ≫ quotProjection (htRings P hP r) (htGenerator P hP r)
    (htGenerator_nat P hP r) 1

/-- 同じ affine 剰余模型を、元の基底環上の余単体的加群として読む。 -/
abbrev affineBaseModules : CosimplicialObject (ModuleCat.{u} A) :=
  toModules A (reducedModel P hP r) (affineBaseCoefficients P hP r)

/-- 各項は、元の基底環の p 作用についても導来完備である。 -/
theorem affineBaseModules_complete (n : SimplexCategory) :
    IsModuleComplete A (p : A) ((affineBaseModules P hP r).obj n) := by
  let V := (htCech P hP r).obj n
  let T := V.B ⧸ V.Q.ideal
  let g : A →+* T := V.toHom.quotientMap.comp (Ideal.Quotient.mk P.ideal)
  letI := g.toAlgebra
  have hT : IsModuleComplete A (p : A) (ModuleCat.of A T) := by
    apply (isModuleComplete_algebraMap_iff A T (p : A) T).mp
    change IsModuleComplete T (g (p : A)) (ModuleCat.of T T)
    rw [map_natCast]
    exact isModuleComplete_principal_quotient_natCast V.B p V.Q.generator V.Q.complete_p
  let e := htResidueIso P hP r n
  let E : ((affineBaseModules P hP r).obj n) ≃ₗ[A] T :=
    { __ := e.toAddEquiv
      map_smul' := fun a x => by
        change (reducedModel P hP r).obj n at x
        change e ((affineBaseCoefficients P hP r).app n a * x) = g a * e x
        rw [map_mul]
        rfl }
  exact isModuleComplete_of_linearEquiv A (p : A) _ _ E.symm hT

variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)
variable (hQ : IsBoundedPrism Q)

/-- 元の基底脚は、選択生成元を保つ剰余の係数変更と可換。 -/
theorem affineBaseCoefficient_square (hg : f.toRingHom P.generator = Q.generator)
    (n : SimplexCategory) :
    ((affineHTCoefficientReduced f hP hQ r hg).app n).hom.comp
        ((affineBaseCoefficients P hP r).app n).hom =
      ((affineBaseCoefficients Q hQ r).app n).hom.comp f.toRingHom := by
  apply RingHom.ext
  intro a
  exact congrArg ((quotProjection (htRings Q hQ r) (htGenerator Q hQ r)
    (htGenerator_nat Q hQ r) 1).app n)
      (affineHTCoefficientRings_base f hP hQ r n a)

/-- 元の基底環の標準完備係数拡大後に延長した、同じ affine 剰余模型の射。 -/
def affineBaseCompletedCoefficientMap (hg : f.toRingHom P.generator = Q.generator) :
    letI := f.toRingHom.toAlgebra
    affineBaseModules P hP r ⋙ pCompletedScalarExtensionFunctor p f.toRingHom ⟶
      affineBaseModules Q hQ r := by
  letI := f.toRingHom.toAlgebra
  exact completedCoefficientMap p A B (reducedModel P hP r) (reducedModel Q hQ r)
    (affineBaseCoefficients P hP r) (affineBaseCoefficients Q hQ r)
    (affineHTCoefficientReduced f hP hQ r hg)
    (affineBaseCoefficient_square hP r f hQ hg) (affineBaseModules_complete Q hQ r)

end SerrePositivity.BhattScholze.Prismatic
