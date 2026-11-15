module

public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.PerfectPrismDivision
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Delta.Division.Basic

/-!
# J/d を割る構成の比較

## 概要
既に割れる場合の復元、同じ関係の再添加、段階的添加と一括添加、d 冪ねじれの除去を先に行う場合との同型。
BS 著者版 Proposition 7.2 の除算構成と Corollary 7.3 の普遍性に関わる、完全試験 prism への比較を与える。

## 方針
普遍性から比較射を作り、両合成が恒等射であることを示す。

## 規約
今は主定理の経路にない。

## 使われ方
J/d を割る構成の性質の確認。旧 Prism/Perfection から移した。
-/

universe u v w

/-! ## 既に可除な完全p進完備δ環の除算候補からの復元

distinguished元dについて指定元族が既にdで割り切れる完全p進完備δ環では、
p進完備δ除算候補への標準射が同型。実導来(p,d)完備化の反復とは区別する。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionRecovery

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}
variable (D : DeltaStructure p R) (hD : D.IsPerfect)
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable (d : R) (hd : D.IsDistinguished d) (a : σ → R) (ha : ∀ s, d ∣ a s)

/-- 恒等基底射を一意に延長して得る、具体的な除算候補からの復元射。 -/
def Semiperfectoid.pCompletedDeltaDivisionRetract : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a →+* R :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom D D hD d hd a (RingHom.id R)
    D.isDeltaHom_id ha).choose

/-- 復元射はδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionRetract_isDeltaHom :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a).IsDeltaHom D
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom D D hD d hd a (RingHom.id R)
    D.isDeltaHom_id ha).choose_spec.1.1

/-- 復元射と元の標準射の合成は恒等射。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionRetract_comp_base :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a) =
      RingHom.id R :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom D D hD d hd a (RingHom.id R)
    D.isDeltaHom_id ha).choose_spec.1.2

/-- 標準射と復元射の逆順の合成も恒等射。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionMap_comp_retract :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha) =
      RingHom.id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isAdicComplete D d a
  apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionHom_ext D _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) d hd a
    _ _ ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a).comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract_isDeltaHom D hD d hd a ha))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a).isDeltaHom_id
  rw [RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract_comp_base,
    RingHom.comp_id, RingHom.id_comp]

include hD hd ha in
/-- 既に完全p進完備で、指定元族がdで可除なδ環の標準除算候補射は全単射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionMap_bijective_of_dvd :
    Function.Bijective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a) := by
  have hl : Function.LeftInverse (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a) :=
    fun x ↦ RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract_comp_base D hD d hd a ha) x
  have hr : Function.RightInverse (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a) :=
    fun x ↦ RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_comp_retract D hD d hd a ha) x
  exact ⟨hl.injective, hr.surjective⟩

/-- 完全p進完備な可除δ環と、その具体的なp進完備δ除算候補の同型。 -/
def Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv : R ≃+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a :=
  RingEquiv.ofBijective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_bijective_of_dvd D hD d hd a ha)

/-- 復元同型の順射は標準除算候補射。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv_toRingHom :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).toRingHom =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a := rfl

/-- 復元同型の逆射は選んだ具体的な復元射。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv_symm_toRingHom :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).symm.toRingHom =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha := by
  apply RingHom.ext
  intro x
  apply (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_bijective_of_dvd D hD d hd a ha).1
  change (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).symm x) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract D hD d hd a ha x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_comp_retract D hD d hd a ha) x).symm

/-- 復元同型の逆射もδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv_symm_isDeltaHom :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a).IsDeltaHom D
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv D hD d hd a ha).symm.toRingHom := by
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv_symm_toRingHom]
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRetract_isDeltaHom D hD d hd a ha

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionRecovery

/-! ## 同じ除算関係を候補環内で再添加した場合の復元

任意のδ基底環からの具体的なp進完備δ除算候補に、同じ基底元族の像を再添加する。
その標準射はδ環同型であり、mod d商の標準射とも両立する。
原典の新しいねじれ除去・導来(p,d)完備化・超限反復の停止とは異なる。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionRepeat

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 同じ基底元族の像を再度除算添加した候補への標準射は、具体的な環同型を与える。 -/
def Semiperfectoid.pCompletedDeltaDivisionRepeatEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a ≃+*
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s)) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isAdicComplete D d a
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)
    (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s)) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d a)

/-- 復元同型の順射は二段目の標準除算候補射。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionRepeatEquiv_toRingHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRepeatEquiv D d hd a).toRingHom =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s)) := rfl

/-- 二段目の復元同型の逆もδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionRepeatEquiv_symm_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)
      (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s))).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRepeatEquiv D d hd a).symm.toRingHom := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isAdicComplete D d a
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRecoveryEquiv_symm_isDeltaHom
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)
    (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s)) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d a)

/-- 再添加前後の候補のmod d商の具体的な同型。 -/
def Semiperfectoid.pCompletedDeltaDivisionRepeatQuotientEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a ⧸ Ideal.span {_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d}) ≃+*
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s)) ⧸
        Ideal.span {(_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
          (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s))
          (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d))}) :=
  Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRepeatEquiv D d hd a) (by
    rw [Ideal.map_span, Set.image_singleton]
    rfl)

/-- mod d商同型は代表元に二段目の標準射を適用する。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionRepeatQuotientEquiv_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (x : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionRepeatQuotientEquiv D d hd a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)
        (fun s ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (a s)) x) := rfl

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionRepeat

/-! ## 異なる二つの除算元族の段階的添加と一括添加

BS 著者版 Proposition 7.2のδ除算普遍性を、具体的な完全p進完備δ候補について使う。
aを添加した候補にbの像を添加する二段構成と、a,bを一括添加する候補を比較する。
導来(p,d)完備化の超限反復やperfectoid化とは同定しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionSequential

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- aを添加した候補でbの基底像をさらに添加する、具体的な二段候補。 -/
abbrev Semiperfectoid.SequentialPCompletedDeltaDivision
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (fun t ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (b t))

/-- 二段候補のδ構造は二段目の既存のδ構造。 -/
abbrev Semiperfectoid.sequentialPCompletedDeltaDivisionStructure
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :
    _root_.SerrePositivity.BhattScholze.DeltaStructure p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) (fun t ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (b t))

/-- 元の基底から二段候補への具体的な標準射。 -/
def Semiperfectoid.sequentialPCompletedDeltaDivisionMap
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :
    R →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)
    (fun t ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (b t))).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a)

/-- 二段候補への標準射はδ射。 -/
theorem Semiperfectoid.sequentialPCompletedDeltaDivisionMap_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) (b : τ → R) :
    D.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionStructure D d a b)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap D d a b) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)
    (fun t ↦ _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a (b t))).comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a)

set_option maxHeartbeats 800000 in
-- 二段の完備化型と三つの普遍射の型照合に、既定のheartbeat上限を超える。
/-- 一括添加と二段添加の間には、基底射と両立する一意なδ環同型が存在する。 -/
theorem Semiperfectoid.existsUnique_pCompletedDeltaDivisionSequentialEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    ∃! e : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (Sum.elim a b) ≃+*
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b,
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d (Sum.elim a b)).IsDeltaHom
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionStructure D d a b) e.toRingHom ∧
      e.toRingHom.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (Sum.elim a b)) =
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap D d a b := by
  let D1 := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a
  let j1 := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a
  let d1 := j1 d
  let b1 := fun t ↦ j1 (b t)
  let j2 := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D1 d1 b1
  let E2 := _root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionStructure D d a b
  let c := Sum.elim a b
  let Ec := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d c
  let jc := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d c
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isAdicComplete D d c
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isAdicComplete D1 d1 b1
  have hE2 : E2.IsPerfect := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D1 d1 b1
  have hEc : Ec.IsPerfect := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d c
  have hj1 := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a
  have hd1 : D1.IsDistinguished d1 := hj1.map_isDistinguished hd
  have hdiv (s : σ ⊕ τ) : (j2.comp j1) d ∣ (j2.comp j1) (c s) := by
    cases s with
    | inl s =>
      obtain ⟨x, hx⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d a s
      refine ⟨j2 x, ?_⟩
      change j2 (j1 (a s)) = j2 (j1 d) * j2 x
      rw [hx, map_mul]
    | inr t => exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D1 d1 b1 t
  obtain ⟨f, hf, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom D E2 hE2 d hd c
    (j2.comp j1) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap_isDeltaHom D d a b) hdiv
  have ha (s : σ) : jc d ∣ jc (a s) := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d c (Sum.inl s)
  obtain ⟨k, hk, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom D Ec hEc d hd a jc
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d c) ha
  have hkval (r : R) : k (j1 r) = jc r := RingHom.congr_fun hk.2 r
  have hb (t : τ) : k d1 ∣ k (b1 t) := by
    change k (j1 d) ∣ k (j1 (b t))
    rw [hkval, hkval]
    exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d c (Sum.inr t)
  obtain ⟨g, hg, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom D1 Ec hEc d1 hd1 b1 k hk.1 hb
  have hgf : g.comp f = RingHom.id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d c) := by
    apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionHom_ext D Ec hEc d hd c _ _ (hg.1.comp hf.1) Ec.isDeltaHom_id
    change (g.comp f).comp jc = (RingHom.id _).comp jc
    rw [RingHom.comp_assoc, hf.2, ← RingHom.comp_assoc, hg.2, hk.2, RingHom.id_comp]
  have hfk : f.comp k = j2 := by
    apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionHom_ext D E2 hE2 d hd a _ _ (hf.1.comp hk.1)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D1 d1 b1)
    change (f.comp k).comp j1 = j2.comp j1
    rw [RingHom.comp_assoc, hk.2]
    exact hf.2
  have hfg : f.comp g = RingHom.id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b) := by
    apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionHom_ext D1 E2 hE2 d1 hd1 b1 _ _ (hf.1.comp hg.1) E2.isDeltaHom_id
    change (f.comp g).comp j2 = (RingHom.id _).comp j2
    rw [RingHom.comp_assoc, hg.2, hfk, RingHom.id_comp]
  have hl : Function.LeftInverse g f := fun x ↦ RingHom.congr_fun hgf x
  have hr : Function.RightInverse g f := fun x ↦ RingHom.congr_fun hfg x
  let e := RingEquiv.ofBijective f ⟨hl.injective, hr.surjective⟩
  refine ⟨e, ⟨hf.1, hf.2⟩, ?_⟩
  intro e' he'
  have h : e'.toRingHom = e.toRingHom := by
    apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionHom_ext D E2 hE2 d hd c _ _ he'.1 hf.1
    exact he'.2.trans hf.2.symm
  apply RingEquiv.ext
  intro x
  exact RingHom.congr_fun h x

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionSequential

/-! ## 段階的除算添加の具体的なδ同型とmod d商同型

一意存在定理から具体的な同型を選び、標準基底射との両立を公開する。
導来(p,d)完備化との比較やperfectoid化の存在は仮定しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionSequentialEquiv

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- 一括添加から二段添加への、基底射と両立する具体的な環同型。 -/
def Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (Sum.elim a b) ≃+*
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionSequentialEquiv D d hd a b).choose

/-- 一括添加から二段添加への同型はδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d (Sum.elim a b)).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionStructure D d a b)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv D d hd a b).toRingHom :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionSequentialEquiv D d hd a b).choose_spec.1.1

/-- 同型は元の環からの標準射と両立する。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv_comp_base
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv D d hd a b).toRingHom.comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (Sum.elim a b)) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap D d a b :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionSequentialEquiv D d hd a b).choose_spec.1.2

/-- 二段添加から一括添加への逆同型もδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv_symm_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionStructure D d a b).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d (Sum.elim a b))
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv D d hd a b).symm.toRingHom :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv_isDeltaHom D d hd a b).symm

/-- 一括添加と二段添加のmod d商の具体的な環同型。 -/
def Semiperfectoid.pCompletedDeltaDivisionSequentialQuotientEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (Sum.elim a b) ⧸
      Ideal.span {_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (Sum.elim a b) d}) ≃+*
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b ⧸
        Ideal.span {_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap D d a b d}) :=
  Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv D d hd a b) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    exact congrArg (fun x ↦ ({x} : Set (_root_.SerrePositivity.BhattScholze.Semiperfectoid.SequentialPCompletedDeltaDivision D d a b)))
      (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv_comp_base D d hd a b) d).symm)

/-- 商同型は代表元に具体的なδ同型を適用する。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionSequentialQuotientEquiv_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (x : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (Sum.elim a b)) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialQuotientEquiv D d hd a b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv D d hd a b x) := rfl

/-- mod d商同型も元の環からの標準射と両立する。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionSequentialQuotientEquiv_comp_base
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialQuotientEquiv D d hd a b).toRingHom.comp
      ((Ideal.Quotient.mk _).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (Sum.elim a b))) =
      (Ideal.Quotient.mk _).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap D d a b) := by
  ext r
  change Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv D d hd a b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (Sum.elim a b) r)) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.sequentialPCompletedDeltaDivisionMap D d a b r)
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionSequentialEquiv_comp_base D d hd a b) r)

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionSequentialEquiv

/-! ## 旧dねじれ除去とp進完備δ除算完全化の比較

BS 著者版 Proposition 7.2の旧ねじれ除去商と、具体的なp進完備δ完全化を比較する。
dがdistinguishedなら、除算添加環のp進完備δ完全化と、旧dねじれのδ閉包商を
先に取ってから同じ完全化を施した環は、標準射と両立するδ環同型を持つ。
一般の導来(p,d)完備化や超限反復とは同定しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionTorsion

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 旧dねじれのδ閉包商が誘導する、具体的なp進完備δ完全化間の標準射。 -/
def Semiperfectoid.pCompletedDeltaDivisionTorsionMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a →+*
      _root_.SerrePositivity.BhattScholze.PCompletedDeltaPerfection (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a) :=
  _root_.SerrePositivity.BhattScholze.pCompletedDeltaMap (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D d a) (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)
    (Ideal.Quotient.mk _)
    ((_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D d a).isDeltaHom_quotient_mk _
      ((_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D d a).isStable_deltaClosure _))

/-- 標準比較射はδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionTorsionMap_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionStructure (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a))
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a) :=
  _root_.SerrePositivity.BhattScholze.pCompletedDeltaMap_isDeltaHom _ _ _ _

/-- 標準比較射は元の基底射と可換。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionTorsionMap_comp_base
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a) =
      (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)).comp
        (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D d a) := by
  let DB := _root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D d a
  let DT := _root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a
  let q : _root_.SerrePositivity.BhattScholze.DeltaAdjoinDivision D d a →+* _root_.SerrePositivity.BhattScholze.DeltaDivisionTorsionQuotient D d a := Ideal.Quotient.mk _
  have hq : DB.IsDeltaHom DT q := DB.isDeltaHom_quotient_mk _ (DB.isStable_deltaClosure _)
  have h : (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a).comp (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap DB) =
      (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap DT).comp q := _root_.SerrePositivity.BhattScholze.pCompletedDeltaMap_comp_map DB DT q hq
  change (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a).comp
      ((_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap DB).comp (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap D d a)) =
    (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap DT).comp (q.comp (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap D d a))
  rw [← RingHom.comp_assoc, h, RingHom.comp_assoc]

/-- dがdistinguishedなら、旧dねじれ除去が誘導する標準p進完備δ完全化射は全単射。
逆射はねじれ除去の普遍性と既存完全化の普遍性から作り、両合成を外延性で検証する。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionTorsionMap_bijective
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    Function.Bijective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a) := by
  let DB := _root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure D d a
  let DT := _root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a
  let q : _root_.SerrePositivity.BhattScholze.DeltaAdjoinDivision D d a →+* _root_.SerrePositivity.BhattScholze.DeltaDivisionTorsionQuotient D d a := Ideal.Quotient.mk _
  let jB := _root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap DB
  let jT := _root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap DT
  let f := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a
  let EC := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isAdicComplete D d a
  let := _root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfection_isAdicComplete DT
  have hq : DB.IsDeltaHom DT q := DB.isDeltaHom_quotient_mk _ (DB.isStable_deltaClosure _)
  have hFj : f.comp jB = jT.comp q := _root_.SerrePositivity.BhattScholze.pCompletedDeltaMap_comp_map DB DT q hq
  obtain ⟨k, hk, _⟩ := DB.existsUnique_torsionReductionHom
    (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap D d a d) EC jB (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap_isDeltaHom DB)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_mul_injective D d a hd)
  let g := _root_.SerrePositivity.BhattScholze.pCompletedDeltaLift DT EC (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) k hk.2
  have hgj : g.comp jT = k := _root_.SerrePositivity.BhattScholze.pCompletedDeltaLift_comp_map DT EC
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) k hk.2
  have hgd : (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionStructure DT).IsDeltaHom EC g :=
    _root_.SerrePositivity.BhattScholze.pCompletedDeltaLift_isDeltaHom DT EC (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) k hk.2
  have hfd := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap_isDeltaHom D d a
  have hGF : g.comp f = RingHom.id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a) := by
    apply _root_.SerrePositivity.BhattScholze.pCompletedDeltaHom_ext DB EC (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a)
      _ _ (hgd.comp hfd) EC.isDeltaHom_id
    change (g.comp f).comp jB = (RingHom.id _).comp jB
    rw [RingHom.comp_assoc, hFj, ← RingHom.comp_assoc, hgj, hk.1, RingHom.id_comp]
  have hfk : f.comp k = jT := by
    apply RingHom.ext
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change f (k (q b)) = jT (q b)
    rw [show k (q b) = jB b from RingHom.congr_fun hk.1 b]
    exact RingHom.congr_fun hFj b
  have hFG : f.comp g = RingHom.id (_root_.SerrePositivity.BhattScholze.PCompletedDeltaPerfection DT) := by
    apply _root_.SerrePositivity.BhattScholze.pCompletedDeltaHom_ext DT (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionStructure DT)
      (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfection_isPerfect DT) _ _ (hfd.comp hgd)
      (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionStructure DT).isDeltaHom_id
    change (f.comp g).comp jT = (RingHom.id _).comp jT
    rw [RingHom.comp_assoc, hgj, hfk, RingHom.id_comp]
  have hl : Function.LeftInverse g f := fun x ↦ RingHom.congr_fun hGF x
  have hr : Function.RightInverse g f := fun x ↦ RingHom.congr_fun hFG x
  exact ⟨hl.injective, hr.surjective⟩

/-- 旧dねじれのδ閉包商を前に施す二つの具体的候補の環同型。 -/
def Semiperfectoid.pCompletedDeltaDivisionTorsionEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a ≃+*
      _root_.SerrePositivity.BhattScholze.PCompletedDeltaPerfection (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a) :=
  RingEquiv.ofBijective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap_bijective D d hd a)

/-- 比較同型の順射は旧ねじれ除去商による標準比較射。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionTorsionEquiv_toRingHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionEquiv D d hd a).toRingHom =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a := rfl

/-- 比較同型の逆射もδ射。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionTorsionEquiv_symm_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionStructure (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionEquiv D d hd a).symm.toRingHom :=
  _root_.SerrePositivity.BhattScholze.DeltaStructure.IsDeltaHom.symm (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap_isDeltaHom D d a)

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionTorsion

/-! ## 旧ねじれ除去前後の候補のmod d商と標準射の比較

具体的なp進完備δ完全化の比較同型をmod d商へ誘導し、R/Jからの標準射を比較する。
perfectoid性・IsPerfectoidization・原典の導来(p,d)完備化との同定は未結論。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionTorsionQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 旧ねじれ除去前後の候補環のmod d商を比較する具体的な同型。 -/
def Semiperfectoid.pCompletedDeltaDivisionTorsionQuotientEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a ⧸ Ideal.span {_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d}) ≃+*
      (_root_.SerrePositivity.BhattScholze.PCompletedDeltaPerfection (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a) ⧸
        Ideal.span {(_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)
          (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D d a d))}) :=
  Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionEquiv D d hd a) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)
      (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D d a d))} =
      Ideal.span {_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d)}
    rw [show _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a d) =
      _root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)
        (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D d a d) from
          RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap_comp_base D d a) d])

/-- mod d比較同型は、代表元へ標準比較射を適用する。 -/
@[simp] theorem Semiperfectoid.pCompletedDeltaDivisionTorsionQuotientEquiv_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (x : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionQuotientEquiv D d hd a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap D d a x) := rfl

/-- 旧ねじれ除去商のmod dから、そのp進完備δ完全化のmod dへの標準誘導射。 -/
def Semiperfectoid.deltaDivisionTorsionToCompletedQuotientMap
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) :
    (_root_.SerrePositivity.BhattScholze.DeltaDivisionTorsionQuotient D d a ⧸ Ideal.span {_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D d a d}) →+*
      (_root_.SerrePositivity.BhattScholze.PCompletedDeltaPerfection (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a) ⧸
        Ideal.span {(_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)
          (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionMap D d a d))}) :=
  Ideal.quotientMap _ (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a)) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span (Set.mem_singleton _))

/-- 旧ねじれ除去商の標準誘導射は、代表元に完全化の標準射を適用する。 -/
@[simp] theorem Semiperfectoid.deltaDivisionTorsionToCompletedQuotientMap_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (a : σ → R) (x : _root_.SerrePositivity.BhattScholze.DeltaDivisionTorsionQuotient D d a) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaDivisionTorsionToCompletedQuotientMap D d a (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _
        (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaDivisionTorsionStructure D d a) x) := rfl

/-- 任意のR/Jからの二つの標準射は、上の具体的なmod d比較同型で一致する。 -/
theorem Semiperfectoid.pCompletedDeltaDivisionTorsionQuotientEquiv_comp_base
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionQuotientEquiv D d hd (fun x : J ↦ (x : R))).toRingHom.comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionQuotientMap D d J) =
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaDivisionTorsionToCompletedQuotientMap D d (fun x : J ↦ (x : R))).comp
          (_root_.SerrePositivity.BhattScholze.deltaDivisionQuotientMap D d J) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionQuotientMap_mk,
    _root_.SerrePositivity.BhattScholze.deltaDivisionQuotientMap_mk, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaDivisionTorsionToCompletedQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionTorsionMap_comp_base D d (fun x : J ↦ (x : R))) r)

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionTorsionQuotient
