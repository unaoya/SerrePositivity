module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionCategory
public import SerrePositivity.DifferentialGraded.Category.Components

/-!
概要：KST §3.1 の係数制限後の合成を局所係数環で計算する。
方針：係数制限の lax tensor の純 tensor 公式と局所合成の双線形性を使う。
規約：局所係数 scalar は共通基底環の scalar と区別する。
使われ方：O(m) の Hom 自己同型が図式係数圏の合成を保つことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory HomologicalComplex DifferentialGraded DifferentialGraded.ScalarExtension

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 概要：共通基底環への係数制限は通常順の斉次合成の値を保つ。
方針：移送された合成の lax tensor 成分を純 tensor 上で評価する。
規約：KST §3.1。使われ方：局所係数環の双線形性による捻りの合成計算。 -/
theorem restrictedForward_eq {D : Type v} [DGCategory B D]
    {x y z : D} {p q n : ℤ} (f : GradedHom B x y p) (g : GradedHom B y z q)
    (h : p + q = n) :
    forward R (D := DGRestriction (algebraMap R B) D) f g h = forward B f g h := by
  change (eComp (Complex B) x y z).f n
    ((Functor.LaxMonoidal.μ (restriction (algebraMap R B))
      (homObject B D x y) (homObject B D y z)).f n
        (ιTensorObj ((restriction (algebraMap R B)).obj (homObject B D x y))
          ((restriction (algebraMap R B)).obj (homObject B D y z))
          p q n h (f ⊗ₜ[R] g))) = _
  rw [restriction_μ_apply]
  rfl

/-- 概要：局所 dg 合成は二つの局所 scalar の積に関して双線形。
方針：tensor の scalar 公式と合成成分の線形性を使う。
規約：KST §3.1。使われ方：半線形な遷移後の二つの捻り単元をまとめる。 -/
theorem localForward_smul {D : Type v} [DGCategory B D]
    {x y z : D} {p q n : ℤ} (s t : B)
    (f : GradedHom B x y p) (g : GradedHom B y z q) (h : p + q = n) :
    forward B (s • f) (t • g) h = (s * t) • forward B f g h := by
  unfold forward
  rw [TensorProduct.smul_tmul_smul]
  change ((eComp (Complex B) x y z).f n).hom
    ((ιTensorObj (homObject B D x y) (homObject B D y z) p q n h).hom
      ((s * t) • (f ⊗ₜ[B] g))) = _
  rw [map_smul, map_smul]

end SerrePositivity.KST.DerivedBlowup
