module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import SerrePositivity.BhattScholze.Delta.Free.PolynomialDelta
public import Mathlib.Logic.Function.Iterate

/-! # 自由整数δ環の普遍性

任意のδ環と生成元の指定から、δの反復像を座標へ評価する一意なδ射を構成する。
BS著者版Lemma 2.11の整数係数の普遍性。pねじれを持つ終域も許す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {σ : Type u} {A : Type v} [CommRing A]

/-- 指定した元族の反復δ像へ、自由環の各座標を評価する環準同型。 -/
def freeDeltaEval (D : DeltaStructure p A) (a : σ → A) : FreeDeltaRing σ →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) (fun v ↦ D.delta^[v.2] (a v.1))

/-- 自由δ環の評価射はx_(s,n)をδ^n(a_s)へ送る。 -/
@[simp] theorem freeDeltaEval_X (D : DeltaStructure p A) (a : σ → A) (s : σ) (n : ℕ) :
    freeDeltaEval D a (MvPolynomial.X (s, n)) = D.delta^[n] (a s) := by
  simp [freeDeltaEval]

/-- 自由δ環の評価射はδと可換。W₂切断の二つの環準同型を生成元上で比較する。
終域のp正則性は仮定せず、単なるFrobenius可換性だけでδ射と判定しない。 -/
theorem freeDeltaEval_isDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    (freeDeltaStructure p σ).IsDeltaHom D (freeDeltaEval D a) := by
  apply DeltaStructure.isDeltaHom_mvPolynomial_of_sectionHom_comp_C _ _ _
    (Subsingleton.elim _ _)
  rintro ⟨s, n⟩
  rw [freeDeltaStructure_delta_X, freeDeltaEval_X, freeDeltaEval_X,
    Function.iterate_succ_apply']

/-- 自由δ環からのδ射の生成元像は、初期座標の像の反復δとなる。 -/
theorem freeDeltaHom_X_iterates (D : DeltaStructure p A) (f : FreeDeltaRing σ →+* A)
    (hf : (freeDeltaStructure p σ).IsDeltaHom D f) (s : σ) (n : ℕ) :
    f (MvPolynomial.X (s, n)) = D.delta^[n] (f (MvPolynomial.X (s, 0))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← freeDeltaStructure_delta_X p σ s n, hf, ih, Function.iterate_succ_apply']

/-- 任意のδ環と元族a_sについて、x_(s,0)をa_sへ送るδ射が一意に存在する。
整数係数の自由δ環の普遍性（BS Lemma 2.11の整数係数部分）。 -/
theorem existsUnique_freeDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    ∃! f : FreeDeltaRing σ →+* A,
      (freeDeltaStructure p σ).IsDeltaHom D f ∧
        ∀ s : σ, f (MvPolynomial.X (s, 0)) = a s := by
  refine ⟨freeDeltaEval D a, ⟨freeDeltaEval_isDeltaHom D a, ?_⟩, ?_⟩
  · intro s
    simp
  · intro f hf
    apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
    rintro ⟨s, n⟩
    rw [freeDeltaHom_X_iterates D f hf.1 s n, hf.2 s, freeDeltaEval_X]

end SerrePositivity.BhattScholze
