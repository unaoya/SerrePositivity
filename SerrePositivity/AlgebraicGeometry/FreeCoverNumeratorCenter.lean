module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FiniteFlatFreeNeighborhood
public import Mathlib.RingTheory.Localization.Ideal

/-!
概要：KST §5、Stacks 0815 の境界外の自由な基本開被覆から元の環の中心を選ぶ。
方針：局所化された環の係数の分子を取り、それらでイデアルを生成する。
規約：元の環の Noether 性はこの中心の構成には不要。
使われ方：境界外で平坦な有限加群を自由な場合へ還元する最初の blowup。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R)

/--
概要：境界外の有限個の係数の分子が生成するイデアル。
方針：一元局所化の分子の選択を有限族に適用する。
規約：KST §5、Stacks 0815、分母は境界元の冪。
使われ方：自由化被覆を元の環上の blowup 中心に降ろす。
-/
def freeCoverNumeratorIdeal (s : Finset (Localization.Away f)) : Ideal R :=
  Ideal.span (Set.range (fun i : s => (IsLocalization.Away.sec f i.val).1))

/--
概要：分子中心は有限生成。
方針：有限型で添字付けされた生成集合の有限性を使う。
規約：KST §5、Stacks 0815、環の Noether 性は不要。
使われ方：最初の blowup の有限生成中心。
-/
theorem freeCoverNumeratorIdeal_fg (s : Finset (Localization.Away f)) :
    (freeCoverNumeratorIdeal f s).FG :=
  Submodule.fg_span (Set.finite_range _)

/--
概要：元の係数族が単位イデアルを生成すれば分子中心も境界外で単位イデアルになる。
方針：係数とその分子の像が単元倍であることを使う。
規約：KST §5、Stacks 0815、像イデアルの等式を主張する。
使われ方：中心の admissible 性に必要な冪の所属。
-/
theorem freeCoverNumeratorIdeal_map_eq_top (s : Finset (Localization.Away f))
    (hs : Ideal.span (s : Set (Localization.Away f)) = ⊤) :
    (freeCoverNumeratorIdeal f s).map (algebraMap R (Localization.Away f)) = ⊤ := by
  apply top_unique
  apply le_trans hs.ge
  apply Ideal.span_le.mpr
  intro x hx
  have hnum : algebraMap R (Localization.Away f) (IsLocalization.Away.sec f x).1 ∈
      (freeCoverNumeratorIdeal f s).map (algebraMap R (Localization.Away f)) :=
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)
  exact (Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst f x)).mp hnum

/--
概要：境界外で単位イデアルとなるイデアルは境界元の一つの冪を含む。
方針：局所化像の一の所属を分母消去の判定で元の環へ戻す。
規約：KST §5、Stacks 0815、境界元の正則性は不要。
使われ方：中心が D(f) を避けることとチャート上の可逆性の計算。
-/
theorem exists_pow_mem_of_away_map_eq_top (I : Ideal R)
    (hI : I.map (algebraMap R (Localization.Away f)) = ⊤) :
    ∃ n : ℕ, f ^ n ∈ I := by
  have h1 : algebraMap R (Localization.Away f) 1 ∈
      I.map (algebraMap R (Localization.Away f)) := by rw [hI]; trivial
  obtain ⟨r, hr, hrI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers f) (Localization.Away f) I 1).mp h1
  obtain ⟨n, rfl⟩ := hr
  exact ⟨n, by simpa using hrI⟩

/--
概要：境界外の有限表示平坦加群の自由化被覆と、その分子中心の冪の所属を選ぶ。
方針：自由な基本開の有限被覆を選び、分子中心の局所化が単位イデアルとなることを使う。
規約：KST §5、Stacks 0815、自由化する加群は局所化された環上の加群。
使われ方：各生成元チャートの境界外を自由な場合へ還元する。
-/
theorem exists_freeCoverNumeratorCenter (N : Type*) [AddCommGroup N]
    [Module (Localization.Away f) N] [Module.FinitePresentation (Localization.Away f) N]
    [Module.Flat (Localization.Away f) N] :
    ∃ s : Finset (Localization.Away f),
      (∀ i : s, Module.Free (Localization.Away i.val) (LocalizedModule.Away i.val N)) ∧
      ∃ n : ℕ, f ^ n ∈ freeCoverNumeratorIdeal f s := by
  obtain ⟨s, hs, hspan⟩ := exists_finset_freeLocalizations (R := Localization.Away f) N
  exact ⟨s, fun i => hs i.val i.property,
    exists_pow_mem_of_away_map_eq_top f _ (freeCoverNumeratorIdeal_map_eq_top f s hspan)⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
