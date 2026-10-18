module

public import SerrePositivity.KST.DerivedBlowup.RestrictionRingHomTransport

/-!
概要：KST §3.1 の代数射に沿う半線形 dg 関手を共通基底環上の dg 関手にする。
方針：基底環への係数制限に標準合成比較と代数射の係数保存の移送を合成する。
規約：新しい dg 構造は作らず、既存の係数制限を用いる。
使われ方：全有限重なりを共通基底環上の dg 代数図式へ束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- 概要：代数射と基底環の構造射の合成は目標の構造射に等しい。
方針：各基底係数で代数射の係数保存を使う。
規約：KST §3.1。使われ方：共通基底環への dg 制限の行先の同定。 -/
theorem baseRestrictionRingHom_comp (f : A →ₐ[R] B) :
    f.toRingHom.comp (algebraMap R A) = algebraMap R B := by
  ext r
  exact f.commutes r

/-- 概要：代数射に沿う半線形 dg 関手を共通基底環上の dg 関手にする。
方針：基底制限した元の関手に、二段の制限比較と構造射の等式移送を合成する。
規約：KST §3.1。使われ方：有限重なりの dg 図式の共通係数化。 -/
def baseRestrictionDGFunctor (f : A →ₐ[R] B)
    {D : Type v} {E : Type w} [DGCategory A D] [DGCategory B E]
    (F : DGFunctor A D (DGRestriction f.toRingHom E)) :
    DGFunctor R (DGRestriction (algebraMap R A) D) (DGRestriction (algebraMap R B) E) :=
  EnrichedFunctor.comp (Complex R)
    (EnrichedFunctor.comp (Complex R) (restrictDGFunctor (algebraMap R A) F)
      (restrictionCompositionDGFunctor (algebraMap R A) f.toRingHom E))
    (restrictionRingHomTransportDGFunctor (baseRestrictionRingHom_comp f) E)

/-- 概要：共通基底環への制限は元の dg 関手の対象の像を保つ。
方針：標準制限比較と環射等式移送の対象公式を使う。
規約：KST §3.1。使われ方：共通基底環上の遷移の合成での対象の照合。 -/
theorem baseRestrictionDGFunctor_obj (f : A →ₐ[R] B)
    {D : Type v} {E : Type w} [DGCategory A D] [DGCategory B E]
    (F : DGFunctor A D (DGRestriction f.toRingHom E)) (x : D) :
    (baseRestrictionDGFunctor f F).obj x = F.obj x :=
  restrictionRingHomTransportDGFunctor_obj _ E _

/-- 概要：共通基底環への制限は外積模型への関手の Hom の元の像を変えない。
方針：二つの標準制限比較を計算し、環射等式移送の成分公式を使う。
規約：KST §3.1。使われ方：有限重なり dg 関手の共通基底環上の合成則。 -/
theorem baseRestrictionDGFunctor_exterior_apply (f : A →ₐ[R] B)
    {D : Type v} [DGCategory A D] {M : Type u} [AddCommGroup M] [Module B M]
    (d : M →ₗ[B] B) (F : DGFunctor A D (DGRestriction f.toRingHom (ExteriorKoszulObject d)))
    (x y : D) (q : ℤ) (z : (homObject A D x y).X q) :
    (((baseRestrictionDGFunctor f F).map x y).f q) z = ((F.map x y).f q) z := by
  change (((restrictionRingHomTransportDGFunctor (baseRestrictionRingHom_comp f)
    (ExteriorKoszulObject d)).map _ _).f q) (((F.map x y).f q) z) = _
  exact restrictionRingHomTransportDGFunctor_exterior_apply _ d _ _ q _

end SerrePositivity.KST.DerivedBlowup
