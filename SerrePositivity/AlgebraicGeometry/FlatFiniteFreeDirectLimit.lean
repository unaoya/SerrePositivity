module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FlatFiniteFreeSequence
public import SerrePositivity.AlgebraicGeometry.LinearSequenceDirectLimit

/-!
概要：KST §5、Stacks 05DP・059X の Noether 基底上の可算生成平坦加群の有限自由直極限表示。
方針：構成済みの近似列へ、評価の核が直後に消える一般の直極限比較を適用する。
規約：実際の有限自由列と線形同型を構成し、射影性は結論に含めない。
使われ方：Mittag–Leffler 性の有限自由列による判定の入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：生成元列から構成した平坦加群の有限自由近似列の直極限は、元の加群と実際に線形同型。
方針：評価の可換式、核消去、像の被覆を直極限の一般比較へ渡す。
規約：KST §5、Stacks 05DP・059X、Noether 基底と実際の生成元列を入力する。
使われ方：可算生成平坦加群を有限自由列の直極限として扱う。
-/
def flatFiniteFreeDirectLimitEquiv
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (g : ℕ → M) (hg : Submodule.span R (Set.range g) = ⊤) :
    DirectLimit (fun n => Fin (flatFiniteFreeStage (R := R) g n).rank →₀ R)
      (linearSequenceMap R _ (flatFiniteFreeTransition (R := R) g)) ≃ₗ[R] M :=
  linearSequenceDirectLimitEquiv R _ (flatFiniteFreeTransition (R := R) g)
    (fun n => (flatFiniteFreeStage (R := R) g n).eval)
    (flatFiniteFreeTransition_eval g) (flatFiniteFreeTransition_ker g)
    (iSup_range_flatFiniteFreeStage g hg)

/--
概要：Noether 基底上の可算生成平坦加群は、有限自由加群の自然数列の直極限として表せる。
方針：可算生成集合を自然数で列挙し、構成済みの近似列と実際の直極限同型を選ぶ。
規約：KST §5、Stacks 05DP・059X、各段階の階数と実際の遷移写像を返す。
使われ方：可算生成平坦 Mittag–Leffler 加群の射影性判定への存在形の入力。
-/
theorem exists_finiteFree_sequence_directLimit_equiv
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (hM : HasCountableGeneratingSet R M) :
    ∃ (d : ℕ → ℕ) (a : ∀ n, (Fin (d n) →₀ R) →ₗ[R] (Fin (d (n + 1)) →₀ R)),
      Nonempty (DirectLimit (fun n => Fin (d n) →₀ R) (linearSequenceMap R _ a) ≃ₗ[R] M) := by
  obtain ⟨g, hg⟩ := hM.exists_nat_spanning
  exact ⟨fun n => (flatFiniteFreeStage (R := R) g n).rank,
    flatFiniteFreeTransition (R := R) g, ⟨flatFiniteFreeDirectLimitEquiv g hg⟩⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
