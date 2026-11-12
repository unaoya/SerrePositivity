module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SourceQuotientNaturality

/-!
# 全入力における対称群作用の照合

HA 3.2.4.7 の自由比較で、Schur 表示と二色入力表示の同じ置換作用を照合する。
BS-W16 の型一覧 L04a。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- Schur 側と二色入力側の対称群作用は、元の複体上で等しい。 -/
lemma binaryTensorInputAction_eq (R : Type u) [CommRing R]
    (X Y : Complex R) (r : ℕ) :
    finiteBijectionComplexAction (bijectionFunctor (X ⊞ Y)) r =
      binaryTensorPowerAction X Y r
        (MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
          Equiv.Perm (Fin r)).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply End.ext
  exact bijectionFunctor_map_permutation (X ⊞ Y) r g.down

end SerrePositivity.EInfinity.BarrattEccles
