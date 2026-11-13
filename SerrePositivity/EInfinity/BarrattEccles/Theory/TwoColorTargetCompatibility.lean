module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ProductQuotientCompatibility

/-!
# 二色のテンソル側の指定商の照合

HA 3.2.4.7。二色係数の表示同型を元の指定商写像へ適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (R : Type u) [CommRing R] (X Y : Complex R) (m n : ℕ)

set_option maxHeartbeats 800000 in
-- 作用の等式による余不変表示の運搬が、既定の 200000 heartbeats を超えるため。
/-- 二色の表示同型は、四因子の交換の後の二つの指定商に一致する。 -/
lemma twoColorTargetSchurIso_quotient :
    coinvariantTotalQuotient
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
      (tensorComplexAction (twoColorLeftAction R m n) (twoColorRightAction R m n)) ≫
      (twoColorTargetSchurIso R X Y m n).hom ≫
      ((schurArityInputCoinvariantIso R X m).hom ⊗ₘ
        (schurArityInputCoinvariantIso R Y n).hom) =
    tensorμ (power X m) (power Y n) ((operad R).arity m) ((operad R).arity n) ≫
      (actionCoinvariantQuotient (tensorComplexAction
        (finiteBijectionComplexAction (bijectionFunctor X) m) (arityComplexAction R m)) ⊗ₘ
       actionCoinvariantQuotient (tensorComplexAction
        (finiteBijectionComplexAction (bijectionFunctor Y) n) (arityComplexAction R n))) := by
  simp only [twoColorTargetSchurIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id, tensorHom_id,
    id_whiskerRight, Category.comp_id]
  rw [← Category.assoc, coinvariantTotalQuotient_comparison]
  rw [← actionCoinvariantQuotient]
  simp only [Functor.mapIso_hom,
    representationTensorShuffleIso, representationCochainIso]
  rw [← Category.assoc, actionCoinvariantQuotient_naturality, Category.assoc]
  let a := tensorComplexAction
    (finiteBijectionComplexAction (bijectionFunctor X) m) (arityComplexAction R m)
  let b := tensorComplexAction
    (finiteBijectionComplexAction (bijectionFunctor Y) n) (arityComplexAction R n)
  let t := tensorComplexAction
    (a.comp (MonoidHom.fst (ULift.{u} (Equiv.Perm (Fin m)))
      (ULift.{u} (Equiv.Perm (Fin n)))))
    (b.comp (MonoidHom.snd (ULift.{u} (Equiv.Perm (Fin m)))
      (ULift.{u} (Equiv.Perm (Fin n)))))
  have ht : tensorComplexAction
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorLeftAction R m n))
      (tensorComplexAction (twoColorRightInputAction Y m n) (twoColorRightAction R m n)) =
        t.comp (twoColorProjectionEquiv m n).toMonoidHom := by
    rw [twoColorLeftInputAction_sequence R X m n, twoColorRightInputAction_sequence R Y m n]
    rfl
  have hq := actionCoinvariantQuotient_transport _ _ ht
  simp only [Functor.mapIso_hom] at hq
  rw [reassoc_of% hq]
  rw [reassoc_of% coinvariantGroupChangeComplexIso_quotient t (twoColorProjectionEquiv m n)]
  rw [productCoinvariantComplexIso_quotient]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
