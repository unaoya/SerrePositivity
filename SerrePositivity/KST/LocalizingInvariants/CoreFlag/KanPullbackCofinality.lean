module
public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.KanPullbackFibers
public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.KanFibrationVanishing
public import SerrePositivity.KST.SConstruction.Cofinality.KanPullbackCofinalityInput

/-!
概要：K-cof 所有の一般 Kan 引き戻し共終性入力を長完全列から証明する。
方針：右列の fiber の正次数消滅を基点付き fiber 同型で左列へ渡す。
規約：結論は既存の Prop そのもの。元の第一射影の誘導写像を保持する。
使われ方：Sp-8 (3)、K-cof への供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open Spectra

/-- 厳密引き戻しの fiber の正次数は、右列の消滅から一意となる。 -/
lemma pullback_positive_fiber_subsingleton
    {P X E B : SSet.{u}} [KanComplex P] [KanComplex X] [KanComplex E] [KanComplex B]
    (q : P ⟶ X) (s : P ⟶ E) (g : X ⟶ B) (p : E ⟶ B)
    (h : IsPullback q s g p) [Fibration q] [Fibration p]
    (hE : ∀ n (e : E _⦋0⦌), Subsingleton (KanHomotopy E n e))
    (hB : ∀ n, 1 < n → ∀ b : B _⦋0⦌, Subsingleton (KanHomotopy B n b))
    (a : P _⦋0⦌) (n : ℕ) (hn : 0 < n) :
    Subsingleton (KanHomotopy (KanFiber q (q.app _ a)) n (fiberPoint q a)) := by
  have := fibration_positive_fiber_subsingleton p hE hB (s.app _ a) n hn
  exact Function.Injective.subsingleton
    (KanHomotopy.equivOfIso n (pullbackFiberIso h a) (pullbackFiberIso_point h a)).injective

/-- K-cof の一般 Kan 引き戻し共終性入力の実証明。 -/
theorem kanPullbackCofinalityInput : SConstruction.Cofinality.KanPullbackCofinalityInput.{u} := by
  intro P X E B _ _ _ _ q s g p h hp hE hB a
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have : Fibration q := pullback_fibration h hp
  have hf (n : ℕ) (hn : 0 < n) :=
    pullback_positive_fiber_subsingleton q s g p h hE hB a n hn
  refine ⟨fibration_map_injective_of_fiber_subsingleton q a 1 (by omega) (hf 1 (by omega)), ?_⟩
  intro n hn
  refine ⟨fibration_map_injective_of_fiber_subsingleton q a n (by omega) (hf n (by omega)), ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact fibration_map_surjective_of_fiber_subsingleton q a k (hf k (by omega))

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
