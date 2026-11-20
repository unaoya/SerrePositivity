module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：filtered colimit での有限単体データの相対因子分解と Kan 性。
方針：有限単体集合の有限表示性により、写像と等式を十分後の段へ移す。
規約：通常の filtered colimit についての補題であり、telescope との比較は別に証明する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の telescope の π_* 計算。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open _root_.SerrePositivity.KST.Spectra

noncomputable section

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)

include hc in
/-- 概要：filtered colimit への有限な相対写像データは一つの後続段で実現できる。
方針：大きい有限対象の写像を一段へ下ろし、小さい有限対象上の等式を後続段で成立させる。
規約：i の単射性と各段の Kan 性は不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。基点と境界を保つ代表単体の因子分解。 -/
theorem finite_relative_factorization {A B : SSet.{u}} [A.Finite] [B.Finite]
    (i : A ⟶ B) (j : J) (a : A ⟶ F.obj j) (b : B ⟶ c.pt)
    (h : a ≫ c.ι.app j = i ≫ b) :
    ∃ (k : J) (v : j ⟶ k) (q : B ⟶ F.obj k),
      i ≫ q = a ≫ F.map v ∧ q ≫ c.ι.app k = b := by
  obtain ⟨l, q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc b
  obtain ⟨k, v, w, hw⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc a (i ≫ q) (by
    rw [Category.assoc, hq, h])
  refine ⟨k, v, q ≫ F.map w, ?_, ?_⟩
  · simpa only [Category.assoc] using hw.symm
  · rw [Category.assoc, c.w w, hq]

include hc in
/-- 概要：有限個の制限の等式を保ちながら有限対象からの射を一つの段へ下ろす。
方針：制限の定義域の有限余積を取り、相対因子分解を一度適用する。
規約：制限の像が交わる場合も互換性の追加入力は不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。RelStruct の全ての面を同時に実現する。 -/
theorem finite_equations_factorization {A B : SSet.{u}} [A.Finite] [B.Finite]
    {m : ℕ} (i : Fin m → (A ⟶ B)) (j : J) (a : Fin m → (A ⟶ F.obj j))
    (b : B ⟶ c.pt) (h : ∀ t, a t ≫ c.ι.app j = i t ≫ b) :
    ∃ (k : J) (v : j ⟶ k) (q : B ⟶ F.obj k),
      (∀ t, i t ≫ q = a t ≫ F.map v) ∧ q ≫ c.ι.app k = b := by
  let P : Fin m → SSet.{u} := fun _ ↦ A
  have hc' : Sigma.desc a ≫ c.ι.app j = Sigma.desc i ≫ b := by
    apply Sigma.hom_ext
    intro t
    simpa only [Sigma.ι_comp_desc_assoc] using h t
  obtain ⟨k, v, q, hq, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.finite_relative_factorization hc (Sigma.desc i) j
    (Sigma.desc a) b hc'
  refine ⟨k, v, q, ?_, hb⟩
  intro t
  have ht := congrArg (fun z : (∐ P) ⟶ F.obj k ↦ Sigma.ι P t ≫ z) hq
  simpa only [Sigma.ι_comp_desc_assoc] using ht

include hc in
/-- 概要：Kan 複体の filtered colimit は Kan。
方針：有限なホーンからの射を一つの段へ下ろし、その段の Kan 充填を合成する。
規約：単射な遷移射を仮定しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。L9d の段ごとの Kan colimit。 -/
theorem kanComplex_of_filtered_isColimit [∀ j, KanComplex (F.obj j)] : KanComplex c.pt := by
  rw [KanComplex.iff]
  intro n i fs hf
  obtain ⟨j, t, ht⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc hf.desc
  obtain ⟨s, hs⟩ := KanComplex.hornFilling t
  have h : (horn (n + 1) i).ι ≫ (s ≫ c.ι.app j) = hf.desc := by
    rw [← Category.assoc, ← hs, ht]
  refine ⟨s ≫ c.ι.app j, fun k hk ↦ ?_⟩
  rw [← horn.ι_ι_assoc i k hk, h]
  exact hf.ι_desc k hk

/-- 概要：Kan 複体の filtered diagram の選ばれた余極限は Kan。
方針：余極限 cocone に有限ホーンによる充填を適用する。
規約：通常の圏論的余極限の Kan 性。
使われ方：Goerss–Jardine I §7、HA §1.4.2。telescope の比較対象。 -/
@[kerodon 03HS]
instance filteredColimit_kanComplex (D : J ⥤ SSet.{u}) [∀ j, KanComplex (D.obj j)] :
    KanComplex (colimit D) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanComplex_of_filtered_isColimit (colimit.isColimit D)

end

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
