module
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor

/-! # 主導来kernel作用と通常kernel作用の比較の自然性

## 概要
主導来kernelを通常代表で計算する同型が、kernel射と二つの作用の水平合成に自然であることを示す。

## 方針
既存の局所化との関手等式を自然同型として用い、Mathlibのexchange則を適用する。

## 規約と注意
局所Hom K-flat条件は不要。全ての通常kernel射を扱う。

## 使われ方
U16aのK-flat代表上の合成比較を、主導来kernel全体に自然な同型へ降ろす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 通常代表での主導来作用の計算同型は、任意のkernel射に自然。 -/
lemma kernelDerivedTensorOnBimoduleIso_naturality
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    (kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f) ≫
        (kernelDerivedTensorOnBimoduleIso A D E P').hom =
      (kernelDerivedTensorOnBimoduleIso A D E P).hom ≫
        kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f := by
  have h := (eqToIso (kernelDerivedTensorFunctor_fac A D E)).hom.naturality f
  simp only [Functor.comp_map] at h
  exact h

variable (F : Type z) [DGCategory A F] [Small.{u} F]

/-- 主導来作用の通常代表比較を水平合成した同型は、両kernel射に自然。 -/
lemma kernelDerivedTensorOnBimoduleIso_hcomp_naturality
    {P P' : BimoduleCategory A E D} {Q Q' : BimoduleCategory A F E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp
        ((kernelDerivedTensorFunctor A D E).map ((bimoduleToDerived A E D).map f))
        ((kernelDerivedTensorFunctor A E F).map ((bimoduleToDerived A F E).map g)) ≫
        (NatIso.hcomp (kernelDerivedTensorOnBimoduleIso A D E P')
          (kernelDerivedTensorOnBimoduleIso A E F Q')).hom =
      (NatIso.hcomp (kernelDerivedTensorOnBimoduleIso A D E P)
          (kernelDerivedTensorOnBimoduleIso A E F Q)).hom ≫
        NatTrans.hcomp
          (kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f)
          (kernelResolutionDerivedTensorMap A E F (moduleCanonicalProjectiveResolution A E) g) := by
  simp only [NatIso.hcomp_hom]
  rw [← NatTrans.exchange, kernelDerivedTensorOnBimoduleIso_naturality,
    kernelDerivedTensorOnBimoduleIso_naturality, NatTrans.exchange]

end SerrePositivity.DifferentialGraded.Morita
