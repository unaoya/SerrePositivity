module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# 小部分圏を消すホモロジー関手の局所化

シフトで安定な部分圏の対象を零に送るホモロジー関手は、その部分圏を錐にもつ
射を同型に送る。長完全列に関する Mathlib の一般結果に帰着する。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]
  (F : C ⥤ A) [F.IsHomological]

/-- シフトで安定な部分圏を消すホモロジー関手は Verdier の分母を反転する。 -/
lemma homological_inverts_of_kills (hF : ∀ X, P X → IsZero (F.obj X)) :
    P.trW.IsInvertedBy F := by
  let := Functor.ShiftSequence.tautological F ℤ
  have hle : P ≤ F.homologicalKernel := by
    intro X hX n
    apply hF
    exact P.le_shift n X hX
  intro X Y f hf
  have h := (F.mem_homologicalKernel_trW_iff f).mp ((P.trW_monotone hle) f hf) 0
  exact (NatIso.isIso_map_iff (F.isoShiftZero ℤ) f).mp h

end SerrePositivity
