module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SphereCoproductBasis

/-!
# 球複体の余積の基底と指定包含

## 概要
Berger–Moerdijk 命題 4.1 の生成元の球複体の余積を、指定された包含で比較する。

## 方針
次数評価の余極限比較と、その逆同型で移した基底を照合する。

## 規約
各球複体には次数零移動した単位の指定基底を使う。

## 使われ方
生成元の余積の包含がセルの重みを保つことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
variable {A : Type u} [CommRing A] {J : Type u} (degree : J → ℤ)

/-- Degree evaluation of a sphere coproduct preserves its specified inclusions. -/
@[reassoc]
lemma sphereCoproductDegreeIso_ι (i : ℤ) (x : J) :
    (Sigma.ι (fun x => complexSphere A (degree x)) x).f i ≫
      (sphereCoproductDegreeIso degree i).hom =
      Sigma.ι (fun x => (complexSphere A (degree x)).X i) x := by
  let V x := complexSphere A (degree x)
  let E := HomologicalComplex.eval (ModuleCat A) (.up ℤ) i
  let h := isColimitCofanMkObjOfIsColimit E V (Sigma.ι V)
    (colimit.isColimit (Discrete.functor V))
  exact IsColimit.comp_coconePointUniqueUpToIso_hom h
    (colimit.isColimit (Discrete.functor _)) (Discrete.mk x)

/-- Each sphere coproduct basis vector is the specified inclusion of its sphere basis vector. -/
lemma sphereCoproductDegreeBasis_apply (i : ℤ) (x : SphereCoproductIndex degree i) :
    sphereCoproductDegreeBasis (A := A) degree i x =
      (Sigma.ι (fun x => complexSphere A (degree x)) x.1).f i
        (sphereDegreeBasis A (degree x.1) i x.2) := by
  let e := sphereCoproductDegreeIso (A := A) degree i
  apply e.toLinearEquiv.injective
  rw [sphereCoproductDegreeBasis, Module.Basis.map_apply]
  change e.toLinearEquiv (e.toLinearEquiv.symm
    (moduleCoproductBasis (fun x => (complexSphere A (degree x)).X i)
      (fun x => sphereDegreeBasis A (degree x) i) x)) = _
  rw [e.toLinearEquiv.apply_symm_apply, moduleCoproductBasis_apply]
  have h := congrArg (fun f => f (sphereDegreeBasis A (degree x.1) i x.2))
    (sphereCoproductDegreeIso_ι (A := A) degree i x.1)
  exact h.symm

end SerrePositivity.EInfinity
