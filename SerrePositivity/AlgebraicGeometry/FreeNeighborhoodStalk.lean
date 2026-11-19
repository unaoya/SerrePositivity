module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FreeStalkRankBaseChange

/-!
概要：KST §5、Stacks 0810・0811 の自由化基本開から元の素点での自由性と階数を得る。
方針：局所化先の素点を選び、自由 locus の局所化公式と自由な素点での階数保存を使う。
規約：元の加群は有限とし、全体での平坦性や環の Noether 性は不要。
使われ方：自由化中心の結論を追加基底変更で保存できる一般点自由性へ変換する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：素点を含む基本開上で階数 r の自由加群なら、その素点で自由かつ局所階数 r。
方針：局所化先の上にある素点で自由性を取り、局所化前後の自由 locus と局所階数を照合する。
規約：KST §5、Stacks 0810・0811、有限性は元の加群に課す。
使われ方：自由化元を返す存在定理を一般点での自由性の述語へ戻す。
-/
theorem freeLocus_and_rankAtStalk_of_away_free
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (P : PrimeSpectrum R) (g : R) (hg : g ∉ P.asIdeal) (r : ℕ)
    (hfree : Module.Free (Localization.Away g) (LocalizedModule.Away g M))
    (hr : Module.finrank (Localization.Away g) (LocalizedModule.Away g M) = r) :
    P ∈ Module.freeLocus R M ∧ Module.rankAtStalk M P = r := by
  let S := Localization.Away g
  let N := LocalizedModule.Away g M
  let : Module.Free S N := hfree
  have hp : P ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S g]
    exact hg
  obtain ⟨Q, hQ⟩ := hp
  have hQfree : Q ∈ Module.freeLocus S N := by rw [Module.freeLocus_eq_univ]; trivial
  have hP : P ∈ Module.freeLocus R M := by
    rw [Module.freeLocus_localization] at hQfree
    change Q.comap (algebraMap R S) ∈ Module.freeLocus R M at hQfree
    rwa [hQ] at hQfree
  refine ⟨hP, ?_⟩
  have hbase := rankAtStalk_baseChange_of_mem_freeLocus (M := M) Q (by rw [hQ]; exact hP)
  let E : N ≃ₗ[S] (S ⊗[R] M) := LocalizedModule.equivTensorProduct (Submonoid.powers g) M
  have hE : Module.rankAtStalk N Q = Module.rankAtStalk (S ⊗[R] M) Q :=
    congrFun (Module.rankAtStalk_eq_of_equiv E) Q
  have hNr : Module.rankAtStalk N Q = r := by
    have hN : Module.rankAtStalk N Q = Module.finrank S N := by simp
    exact hN.trans hr
  calc
    Module.rankAtStalk M P = Module.rankAtStalk M (Q.comap (algebraMap R S)) :=
      congrArg (Module.rankAtStalk M) hQ.symm
    _ = Module.rankAtStalk (S ⊗[R] M) Q := hbase.symm
    _ = Module.rankAtStalk N Q := hE.symm
    _ = r := hNr

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
