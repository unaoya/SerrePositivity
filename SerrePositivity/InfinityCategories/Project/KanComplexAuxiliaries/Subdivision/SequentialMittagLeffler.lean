module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：非空な Mittag–Leffler 逐次逆系の整合族を構成する。
方針：安定した像へ制限した全射な塔で、前段を持ち上げて順次選ぶ。
規約：有限性は仮定しない。選択公理で逐次的に整合する族を作る。
使われ方：Goerss–Jardine VIII §1。twisted 逆系から lim¹ の消滅を導く。
-/

@[expose] public section
universe u
open CategoryTheory Opposite

namespace SerrePositivity.KST.Spectra.SequentialMittagLeffler
end SerrePositivity.KST.Spectra.SequentialMittagLeffler
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.SequentialMittagLeffler

noncomputable section

variable (F : ℕᵒᵖ ⥤ Type u) [∀ j, Nonempty (F.obj j)] (hF : F.IsMittagLeffler)

/-- 安定した像の間の全射で選んだ整合族。 -/
def eventualSection : ∀ n, F.toEventualRanges.obj (op n)
  | 0 => Classical.choice (F.toEventualRanges_nonempty hF (op 0))
  | n + 1 => Classical.choose (F.surjective_toEventualRanges hF
      (homOfLE (Nat.le_succ n)).op (eventualSection n))

/-- 選んだ次段の像は前段そのもの。 -/
lemma eventualSection_comp (n : ℕ) :
    F.toEventualRanges.map (homOfLE (Nat.le_succ n)).op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.eventualSection F hF (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.eventualSection F hF n :=
  Classical.choose_spec (F.surjective_toEventualRanges hF
    (homOfLE (Nat.le_succ n)).op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.eventualSection F hF n))

include hF in
/-- 非空な Mittag–Leffler 逐次逆系には隣接射で整合する族がある。 -/
theorem exists_compatible_family :
    ∃ a : ∀ n, F.obj (op n),
      ∀ n, F.map (homOfLE (Nat.le_succ n)).op (a (n + 1)) = a n := by
  refine ⟨fun n ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.eventualSection F hF n).val, fun n ↦ ?_⟩
  exact congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.eventualSection_comp F hF n)

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
