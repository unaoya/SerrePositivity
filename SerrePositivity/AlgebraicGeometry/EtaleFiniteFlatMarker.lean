module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：平坦な準有限射の指定点を、基底の初等 étale 近傍上の有限射影な部分に分離する。
方針：準有限射の局所有限化を適用し、底変換と局所化で平坦性を保つ。
規約：基底環を Noether とする。
使われ方：滑らかなファイバーの連結成分を追う有限局所自由な標識を作る。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：Noether 基底上の有限型平坦な代数の準有限点は、基底の剰余体を変えない
étale 近傍上で、指定ファイバーが一点の有限射影な開閉部分に入る。
方針：準有限代数の étale 局所有限化の有限部分に、平坦性と有限表示性を移す。
規約：有限部分は冪等元での局所化として表す。
使われ方：有限自由な座標切断を、滑らかな射の étale チャートに引き戻して使う。
-/
theorem exists_etale_finiteProjective_piece_at_quasiFinite
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt R q] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T)
      (y : Ideal T) (_ : y.IsPrime) (_ : y.LiesOver p)
      (e : T ⊗[R] S) (_ : IsIdempotentElem e)
      (w : Ideal (T ⊗[R] S)) (_ : w.IsPrime) (_ : w.LiesOver y),
      w.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ w ∧
      Function.Bijective (Ideal.ResidueField.mapₐ p y (Algebra.ofId _ _) (y.over_def p)) ∧
      Module.Finite T (Localization.Away e) ∧ Module.Projective T (Localization.Away e) ∧
      ∀ w' : Ideal (T ⊗[R] S), w'.IsPrime → w'.LiesOver y → e ∉ w' → w' = w := by
  obtain ⟨T, _, _, hT, y, hy, hyp, e, he, w, hw, hwy, hwq, hwe, hκ, hfinite, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
  let : Module.Flat T (Localization.Away e) := inferInstance
  let : Module.FinitePresentation T (Localization.Away e) :=
    Module.finitePresentation_of_finite T _
  exact ⟨T, _, _, hT, y, hy, hyp, e, he, w, hw, hwy, hwq, hwe, hκ, hfinite,
    Module.Flat.projective_of_finitePresentation, huniq⟩

end SerrePositivity.AlgebraicGeometry
