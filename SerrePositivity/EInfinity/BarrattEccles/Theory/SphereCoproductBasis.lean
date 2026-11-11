module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeBasis
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# セルの sphere の余積の次数付き基底

## 概要
Berger–Moerdijk 命題 4.1 のセルの生成元を、sphere の余積の基底で記録する。

## 方針
各 sphere の指定基底を取り、次数で評価した余積の標準同型を使う。

## 規約
基底の添字はセルの識別子と、その次数で非零な sphere 基底の添字。

## 使われ方
セル代数の Schur 表示の入力と、先行セルへの整礎再帰で付ける重み。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded

variable (A : Type u) [CommRing A]

/-- The singleton index in the degree of the sphere, and the empty index elsewhere. -/
def sphereDegreeIndex (d i : ℤ) : Type u :=
  if i = d then ULift.{u} PUnit.{1} else PEmpty

/-- The specified graded basis of one sphere. -/
def sphereDegreeBasis (d i : ℤ) :
    Module.Basis (sphereDegreeIndex.{u} d i) A ((complexSphere A d).X i) := by
  classical
  by_cases h : i = d
  · subst i
    rw [sphereDegreeIndex, ite_eq_left (show d = d from rfl)]
    exact (Module.Basis.singleton (ULift.{u} PUnit.{1}) A).map
      (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat A))).symm.toLinearEquiv
  · haveI : Subsingleton ((complexSphere A d).X i) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) d (𝟙_ (ModuleCat A)) i h)
    change Module.Basis (if i = d then ULift.{u} PUnit.{1} else PEmpty) A
      ((complexSphere A d).X i)
    rw [ite_eq_right h]
    exact Module.Basis.empty _

variable {A} {J : Type u} (degree : J → ℤ)

/-- Evaluating the coproduct of spheres in a degree gives the coproduct of their modules. -/
def sphereCoproductDegreeIso (i : ℤ) :
    (∐ (fun x => complexSphere A (degree x))).X i ≅
      ∐ (fun x => (complexSphere A (degree x)).X i) := by
  let V x := complexSphere A (degree x)
  let E := HomologicalComplex.eval (ModuleCat A) (.up ℤ) i
  let h := isColimitCofanMkObjOfIsColimit E V (Sigma.ι V)
    (colimit.isColimit (Discrete.functor V))
  exact h.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor _))

/-- The basis labels for the degree of a coproduct of spheres. -/
abbrev SphereCoproductIndex (i : ℤ) := Σ x, sphereDegreeIndex.{u} (degree x) i

/-- The specified graded basis of the actual coproduct of the generator spheres. -/
def sphereCoproductDegreeBasis (i : ℤ) :
    Module.Basis (SphereCoproductIndex degree i) A
      ((∐ (fun x => complexSphere A (degree x))).X i) :=
  (moduleCoproductBasis (fun x => (complexSphere A (degree x)).X i)
    (fun x => sphereDegreeBasis A (degree x) i)).map
      (sphereCoproductDegreeIso degree i).symm.toLinearEquiv

/-- A nonempty sphere basis index fixes the degree of its cell label. -/
lemma sphereCoproductIndex_degree (i : ℤ) (x : SphereCoproductIndex degree i) :
    i = degree x.1 := by
  classical
  by_contra h
  have y := x.2
  change (if i = degree x.1 then ULift.{u} PUnit.{1} else PEmpty) at y
  rw [ite_eq_right h] at y
  exact y.elim

end SerrePositivity.EInfinity
