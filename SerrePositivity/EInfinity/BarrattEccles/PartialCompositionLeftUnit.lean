module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeftUnit
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 部分合成の複体の射の左単位則

概要：Berger–Fresse §1.1.3 の左単位則を arity の移送を含む複体の射の等式として証明する。
方針：左単位子の逆を前合成し、単位と負次数の元の純粋テンソルで評価する。
規約：出力 arity 0+n は既存の等式の射で n へ移す。
使われ方：Barratt–Eccles オペラッドの unit_comp を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：負の次数の純粋テンソルの出力を任意の等しい鎖次数で指定する（Berger–Fresse §1.1.3）。
方針：鎖次数の等式を消去して部分合成の既存の評価公式を使う。
規約：出力は −k、鎖次数の等式は p+q=k である。
使われ方：左単位則の出力次数 0+q を q へ合わせる。 -/
lemma partialComposition_neg_tmul_output (m n : ℕ) (i : Fin (m + 1)) (p q k : ℕ)
    (h : p + q = k) (x : (complex A (m + 1)).X (-(p : ℤ)))
    (y : (complex A n).X (-(q : ℤ))) :
    (partialComposition A m n i).f (-(k : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-(k : ℤ)) (by omega) (x ⊗ₜ[A] y)) =
      (complexXIso A (m + n) k).inv (degreeTransport A (m + n) h
        (shuffleBilinear A m n i p q ((complexXIso A (m + 1) p).hom x)
          ((complexXIso A n q).hom y))) := by
  subst k
  rw [degreeTransport_refl]
  exact partialComposition_neg_tmul A m n i p q x y

/-- 概要：左から単位を代入した部分合成は arity の移送後に元へ戻る（Berger–Fresse §1.1.3）。
方針：単位の0次の値と負の純粋テンソルの公式を使い、鎖次数の左単位則へ帰着する。
規約：出力 arity は 0+n から n へ既存の等式の射で移す。
使われ方：部分合成の左単位則を左単位子の逆像上で計算する。 -/
lemma partialComposition_left_unit_tmul (n q : ℕ) (y : (complex A n).X (-(q : ℤ))) :
    (eqToHom (congrArg (complex A) (Nat.zero_add n))).f (-(q : ℤ))
        ((partialComposition A 0 n 0).f (-(q : ℤ))
          (ιTensorObj (complex A 1) (complex A n) 0 (-(q : ℤ)) (-(q : ℤ)) (by omega)
            ((unit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) ⊗ₜ[A] y))) =
      y := by
  erw [partialComposition_neg_tmul_output A 0 n 0 0 q q (Nat.zero_add q)]
  rw [unit_zero_apply, one_smul]
  have hu : (complexXIso A 1 0).hom
      ((complexXIso A 1 0).inv (normalizedGenerator A 1 0 unitSimplex)) =
        normalizedGenerator A 1 0 unitSimplex :=
    congrArg (fun f => f (normalizedGenerator A 1 0 unitSimplex)) (complexXIso A 1 0).inv_hom_id
  rw [hu, ← normalizedFunctor_arityMap A (Nat.zero_add n)]
  erw [complexXIso_inv_naturality_apply A (m := 0 + n) (n := n)
    (simplicialArityMap (Nat.zero_add n)) q,
    degreeTransport_naturality A _ (Nat.zero_add q), shuffleBilinear_left_unit]
  exact congrArg (fun f => f y) (complexXIso A n q).hom_inv_id

/-- 概要：単位演算への部分合成は arity の移送後に左単位子となる（Berger–Fresse §1.1.3）。
方針：左単位子の逆を前合成し、負の次数は単位の純粋テンソル、正次数は零元で検査する。
規約：既存のコチェインテンソルと arity の等式の射を用いる。
使われ方：Barratt–Eccles オペラッドの左単位則となる。 -/
lemma partialComposition_left_unit (n : ℕ) :
    (unit A ▷ complex A n) ≫ partialComposition A 0 n 0 ≫
        eqToHom (congrArg (complex A) (Nat.zero_add n)) = (λ_ (complex A n)).hom := by
  apply (cancel_epi (λ_ (complex A n)).inv).1
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (eqToHom (congrArg (complex A) (Nat.zero_add n))).f r
    ((partialComposition A 0 n 0).f r
      ((unit A ▷ complex A n).f r ((λ_ (complex A n)).inv.f r y))) = y
  by_cases hr : 0 < r
  · have hy := complex_eq_zero_of_positive A n r hr y
    simp only [hy, map_zero]
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = -(q : ℤ) := ⟨(-r).toNat, by omega⟩
  rw [cochain_leftUnitor_inv_apply A,
    SerrePositivity.DifferentialGraded.whiskerRight_apply (unit A) (complex A n)
      0 (-(q : ℤ)) (-(q : ℤ)) (zero_add _)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) y,
    partialComposition_left_unit_tmul A n q y]

end SerrePositivity.EInfinity.BarrattEccles
