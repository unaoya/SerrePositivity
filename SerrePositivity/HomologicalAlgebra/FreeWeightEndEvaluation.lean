module
public import SerrePositivity.HomologicalAlgebra.LinearWeightEnd
public import Mathlib.LinearAlgebra.Pi

/-!
概要：単位加群を係数とする自由重みの線形 end を、元の複体値図式の評価と同定する。
方針：自由 Yoneda の指定評価に、単位の 1 での評価の線形同値を合成する。
規約：各次数の射は恒等射の生成元での 1 の評価。図式の射への自然性を保持する。
使われ方：HA 1.2.4、G10 の標準単体重みと積 Tot の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 単位加群からの線形 Hom の、1 での評価による自然同型。 -/
def unitLinearHomNatIso :
    (linearCoyoneda A (ModuleCat.{u} A)).obj (op (ModuleCat.of A A)) ≅ 𝟭 (ModuleCat.{u} A) :=
  NatIso.ofComponents (fun M =>
    ((ModuleCat.homLinearEquiv : (ModuleCat.of A A ⟶ M) ≃ₗ[A] (A →ₗ[A] M)) ≪≫ₗ
      LinearMap.ringLmapEquivSelf A A M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl)

/-- 単位 Hom を各複体次数へ適用しても、同じ評価は複体自然同型。 -/
def unitLinearHomComplexNatIso :
    ((linearCoyoneda A (ModuleCat.{u} A)).obj (op (ModuleCat.of A A))).mapHomologicalComplex
      (.up ℤ) ≅ 𝟭 (Complex A) :=
  NatIso.mapHomologicalComplex (unitLinearHomNatIso A) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} A) (.up ℤ)

/-- 自由単位重みからの end の全関手は、元の図式の指定対象での評価。 -/
def freeUnitWeightEndNatIso (j : J) :
    linearWeightEndFunctor A ((freePresheafFunctor J (ModuleCat.of A A)).obj j) ≅
      (evaluation Jᵒᵖ (Complex A)).obj (op j) :=
  freeWeightEndNatIso A (ModuleCat.of A A) j ≪≫
    Functor.isoWhiskerLeft ((evaluation Jᵒᵖ (Complex A)).obj (op j))
      (unitLinearHomComplexNatIso A)

/-- 同じ複体比較の各成分は、恒等射の生成元の 1 による評価。 -/
theorem freeUnitWeightEndNatIso_hom_f_apply (j : J) (X : Jᵒᵖ ⥤ Complex A) (q : ℤ)
    (z : (freePresheafFunctor J (ModuleCat.of A A)).obj j ⟶
      X ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) :
    ((freeUnitWeightEndNatIso A j).hom.app X).f q z =
      (freePresheafHomLinearEquiv (R := A) (ModuleCat.of A A) j
        (X ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q) z) (1 : A) := rfl

end SerrePositivity.HomologicalAlgebra
