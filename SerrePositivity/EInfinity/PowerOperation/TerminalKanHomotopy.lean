module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyConstant
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 終対象 Kan 複体の全ホモトピー類の一元性

DAG XIII §2.2 の cone 比較で使う一般の補助。定数射と恒等射の厳密な一致を使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
open scoped Simplicial
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

lemma terminalKanHomotopy_subsingleton {X : SSet.{u}} [KanComplex X]
    (hX : IsTerminal X) (n : ℕ) (x : X _⦋0⦌) :
    Subsingleton (KanHomotopy X n x) := by
  have he : SSet.const (X := X) x = 𝟙 X := hX.hom_ext _ _
  have ha (a : KanHomotopy X n x) : a = KanHomotopy.point n := by
    have h := map_const n (x := x) (y := x) (by rw [he]; rfl) a
    simpa only [he, KanHomotopy.map_id] using h
  exact ⟨fun a b => (ha a).trans (ha b).symm⟩

lemma kanHomotopy_subsingleton_of_terminal_comparison
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    (hf : SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f)
    (hY : IsTerminal Y) (n : ℕ) (x : X _⦋0⦌) :
    Subsingleton (KanHomotopy X n x) := by
  have := terminalKanHomotopy_subsingleton hY n (f.app _ x)
  exact (hf x n).1.subsingleton

/-- 終対象への同型で、比較射の全単射 RLP を終対象射へ移す。 -/
lemma terminal_rlp_of_terminalComparison {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) (hY : IsTerminal Y) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from X) := by
  let e := hY.uniqueUpToIso terminalIsTerminal
  let ea : Arrow.mk f ≅ Arrow.mk (terminal.from X) :=
    Arrow.isoMk (Iso.refl _) e (by
      simpa using (terminalIsTerminal.hom_ext (f ≫ e.hom) (terminal.from X)).symm)
  exact ((MorphismProperty.monomorphisms SSet.{u}).rlp.arrow_iso_iff ea).mp hf

end SerrePositivity.EInfinity.PowerOperation
