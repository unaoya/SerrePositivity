module

public import SerrePositivity.EInfinity.IntervalCuts.CochainAction
public import SerrePositivity.EInfinity.IntervalCuts.NestedOutputValues
public import SerrePositivity.EInfinity.Surjection.ComplexComposition

/-!
# 実際の合成余作用の辺入力

概要：Berger–Fresse §2.2.6・§3.1 の部分合成則の左辺を実際の区間切断成分へ接続する。
方針：整数複体の語基底の部分合成を評価し、辺入力の既存成分へ戻す。
規約：実際の複体射の合成を評価し、部分合成則は仮定しない。
使われ方：左右両方の実際の複体射を同じ二段切断和で比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

attribute [local implicit_reducible] TensorPowers.power

/-- 概要：語基底と辺での実際の合成余作用は合成語加群の辺成分（BF §3.1）。
方針：部分合成の負次数評価と実際の cochainAction の辺評価を順に使う。
規約：全 arity を扱い、内側 arity の正性を仮定しない。
使われ方：部分合成則の実際の左辺を有限切断和へ移す。 -/
lemma cochainAction_composition_basis_edge {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) :
    ((complexPartialComposition A m n i ▷ interval A) ≫ cochainAction A (m + n)).f
      (-((d + e + 1 : ℕ) : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-((d + e : ℕ) : ℤ)) (-1) (-((d + e + 1 : ℕ) : ℤ)) (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-((d + e : ℕ) : ℤ)) (by omega)
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A] faceVector A edge)) =
      edgeComponent A (m + n) (d + e) (compositionOnWords A u v i) := by
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply]
  erw [complexPartialComposition_neg_tmul A m n i d e]
  simp only [ModuleCat.hom_inv_apply, partialComposition_basis]
  have hf : (show (interval A).X (-1) from faceVector A edge) =
      (intervalXIso A 1).inv (edgeChain A) := by
    unfold faceVector
    rw [faceChain_edge]
    rfl
  have H := cochainAction_neg_edge A (m + n) (d + e)
    ((complexXIso A (m + n) (d + e)).inv (compositionOnWords A u v i)) (faceVector A edge)
  simp only [ModuleCat.hom_inv_apply] at H
  exact H.trans ((congrArg (fun w : (interval A).X (-1) =>
    edgeInputBilinear A (m + n) (d + e) (compositionOnWords A u v i) w) hf).trans
      (edgeInputBilinear_edge A (m + n) (d + e) (compositionOnWords A u v i)))

end SerrePositivity.EInfinity.IntervalCuts
