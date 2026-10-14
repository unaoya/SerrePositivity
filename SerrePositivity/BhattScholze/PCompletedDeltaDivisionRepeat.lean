module

public import SerrePositivity.BhattScholze.PCompletedDeltaDivisionRecovery

/-! # 同じ除算関係を候補環内で再添加した場合の復元

任意のδ基底環からの具体的なp進完備δ除算候補に、同じ基底元族の像を再添加する。
その標準射はδ環同型であり、mod d商の標準射とも両立する。
原典の新しいねじれ除去・導来(p,d)完備化・超限反復の停止とは異なる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 同じ基底元族の像を再度除算添加した候補への標準射は、具体的な環同型を与える。 -/
def pCompletedDeltaDivisionRepeatEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    PCompletedDeltaDivision D d a ≃+*
      PCompletedDeltaDivision (pCompletedDeltaDivisionStructure D d a)
        (pCompletedDeltaDivisionMap D d a d) (fun s ↦ pCompletedDeltaDivisionMap D d a (a s)) := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  exact pCompletedDeltaDivisionRecoveryEquiv (pCompletedDeltaDivisionStructure D d a)
    (pCompletedDeltaDivision_isPerfect D d a) (pCompletedDeltaDivisionMap D d a d)
    ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)
    (fun s ↦ pCompletedDeltaDivisionMap D d a (a s)) (pCompletedDeltaDivisionMap_dvd D d a)

/-- 復元同型の順射は二段目の標準除算候補射。 -/
@[simp] theorem pCompletedDeltaDivisionRepeatEquiv_toRingHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (pCompletedDeltaDivisionRepeatEquiv D d hd a).toRingHom =
      pCompletedDeltaDivisionMap (pCompletedDeltaDivisionStructure D d a)
        (pCompletedDeltaDivisionMap D d a d) (fun s ↦ pCompletedDeltaDivisionMap D d a (a s)) := rfl

/-- 二段目の復元同型の逆もδ射。 -/
theorem pCompletedDeltaDivisionRepeatEquiv_symm_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (pCompletedDeltaDivisionStructure (pCompletedDeltaDivisionStructure D d a)
      (pCompletedDeltaDivisionMap D d a d)
      (fun s ↦ pCompletedDeltaDivisionMap D d a (a s))).IsDeltaHom
      (pCompletedDeltaDivisionStructure D d a)
      (pCompletedDeltaDivisionRepeatEquiv D d hd a).symm.toRingHom := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  exact pCompletedDeltaDivisionRecoveryEquiv_symm_isDeltaHom
    (pCompletedDeltaDivisionStructure D d a) (pCompletedDeltaDivision_isPerfect D d a)
    (pCompletedDeltaDivisionMap D d a d)
    ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)
    (fun s ↦ pCompletedDeltaDivisionMap D d a (a s)) (pCompletedDeltaDivisionMap_dvd D d a)

/-- 再添加前後の候補のmod d商の具体的な同型。 -/
def pCompletedDeltaDivisionRepeatQuotientEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (PCompletedDeltaDivision D d a ⧸ Ideal.span {pCompletedDeltaDivisionMap D d a d}) ≃+*
      (PCompletedDeltaDivision (pCompletedDeltaDivisionStructure D d a)
        (pCompletedDeltaDivisionMap D d a d) (fun s ↦ pCompletedDeltaDivisionMap D d a (a s)) ⧸
        Ideal.span {(pCompletedDeltaDivisionMap (pCompletedDeltaDivisionStructure D d a)
          (pCompletedDeltaDivisionMap D d a d) (fun s ↦ pCompletedDeltaDivisionMap D d a (a s))
          (pCompletedDeltaDivisionMap D d a d))}) :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaDivisionRepeatEquiv D d hd a) (by
    rw [Ideal.map_span, Set.image_singleton]
    rfl)

/-- mod d商同型は代表元に二段目の標準射を適用する。 -/
@[simp] theorem pCompletedDeltaDivisionRepeatQuotientEquiv_mk
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (x : PCompletedDeltaDivision D d a) :
    pCompletedDeltaDivisionRepeatQuotientEquiv D d hd a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionMap (pCompletedDeltaDivisionStructure D d a)
        (pCompletedDeltaDivisionMap D d a d)
        (fun s ↦ pCompletedDeltaDivisionMap D d a (a s)) x) := rfl

end SerrePositivity.BhattScholze
