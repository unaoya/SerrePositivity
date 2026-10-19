module

public import SerrePositivity.KST.Spectra.CosimplicialMatchingFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：余単体図式の終射の相対 matching 射を、通常の matching 射へ同定する。
方針：終図式の matching 射は終対象間の同型であり、その引き戻しの射影も同型。
規約：Reedy fibrancy を通常の matching 射の持ち上げ性として計算する界面。
使われ方：Goerss–Jardine VII §4。loop の Reedy 条件の移送。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.CosimplicialTerminalMatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [HasLimits C]

/-- 終図式の matching 比較は実際の同型。 -/
lemma terminal_isIso (j : SimplexCategory) :
    IsIso ((matchingComparison simplex j).app (⊤_ CosimplicialObject C)) := by
  let E := (evaluation SimplexCategory C).obj j
  let M := matchingEvaluation simplex j (C := C)
  let tE := (terminalIsTerminal (C := CosimplicialObject C)).isTerminalObj E _
  let tM := (terminalIsTerminal (C := CosimplicialObject C)).isTerminalObj M _
  let e := tE.uniqueUpToIso tM
  have he : (matchingComparison simplex j).app (⊤_ CosimplicialObject C) = e.hom :=
    tM.hom_ext _ _
  rw [he]
  infer_instance

/-- 終射の相対 matching は、通常の matching 比較と arrow 同型。 -/
def arrowIso (X : CosimplicialObject C) (j : SimplexCategory) :
    Arrow.mk (relativeMatchingMap simplex j (terminal.from X)) ≅
      Arrow.mk ((matchingComparison simplex j).app X) := by
  let := terminal_isIso (C := C) j
  let e := asIso (pullback.snd
    ((matchingComparison simplex j).app (⊤_ CosimplicialObject C))
    ((matchingEvaluation simplex j).map (terminal.from X)))
  exact Arrow.isoMk (Iso.refl _) e (by
    change 𝟙 _ ≫ (matchingComparison simplex j).app X =
      relativeMatchingMap simplex j (terminal.from X) ≫
        pullback.snd ((matchingComparison simplex j).app (⊤_ CosimplicialObject C))
          ((matchingEvaluation simplex j).map (terminal.from X))
    rw [Category.id_comp]
    exact (pullback.lift_snd _ _ _).symm)

end
end SerrePositivity.KST.Spectra.CosimplicialTerminalMatching
