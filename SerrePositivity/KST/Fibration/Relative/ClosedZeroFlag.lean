module
public import SerrePositivity.KST.Fibration.Relative.ClosedKernelContraction
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.KST.Comparison.DiagramExInfinity

/-!
概要：指定零旗への、関手的 Kan 模型での実収縮。
方針：可縮性を指定点の弱同値へ移し、Kan 標的の実ホモトピーを回収する。
規約：元の射を Ex∞ 単位で送った合成を明記する。使われ方：fiber の零化データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel

namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：選んだ同じ零自己関手の零図式を全旗へ送る。
方針：全 S• の指定点と相対比較の実射を合成。
規約：入力は B・P のみ。使われ方：fiber の固定基点。 -/
def closedKernelZeroFlag {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (Δ[0] : SSet.{u}) ⟶ closedKernelRealization P :=
  toUnit _ ≫ stableZeroSDiagonalPoint (flagAmbient (closedStableModel P)) ≫
    (simplicialDiagonalFunctor.mapIso (closedKernelRelativeSimplicialIso P)).inv ≫
      relativeSWeakStringCoreComparison (closedKernelZeroMap P)

/-- 概要：可縮な元の対象の指定点は局所化同型。
方針：指定点から終射への合成は二つの終対象の同型。
規約：任意の指定点。使われ方：同じ零旗での収縮。 -/
lemma specifiedPoint_isIso {E : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ E)
    (hE : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from E))) :
    IsIso (AnodyneHomotopy.anodyneQ.map z) := by
  let Q := AnodyneHomotopy.anodyneQ
  let e := stdSimplex.isTerminalObj₀.uniqueUpToIso (terminalIsTerminal (C := SSet.{u}))
  have h : Q.map z ≫ Q.map (terminal.from E) = Q.map e.hom := by
    rw [← Q.map_comp]
    exact congrArg Q.map (terminal.hom_ext _ _)
  have hz : Q.map z = Q.map e.hom ≫ inv (Q.map (terminal.from E)) :=
    (IsIso.eq_comp_inv (Q.map (terminal.from E))).2 h
  exact hz.symm ▸ inferInstance

/-- 概要：可縮な対象から Kan 標的への実写像を指定点で零化。
方針：点での前合成の π₀ 単射性と Kan 写像空間のホモトピー判定。
規約：単位を経由する射は呼び出し側で明記。使われ方：指定零旗の実収縮。 -/
lemma specifiedPoint_map_homotopy {E K : SSet.{u}} [KanComplex K]
    (z : (Δ[0] : SSet.{u}) ⟶ E) (g : E ⟶ K)
    (hE : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from E))) :
    Nonempty (SSet.Homotopy (stdSimplex.isTerminalObj₀.from E ≫ z ≫ g) g) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).1
  have hz := EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence z
    (specifiedPoint_isIso z hE)
  apply (hz K).1
  change π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (z ≫ (stdSimplex.isTerminalObj₀.from E ≫ z ≫ g))) =
    π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (z ≫ g))
  have ht : z ≫ stdSimplex.isTerminalObj₀.from E = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← Category.assoc z, ← Category.assoc, ht, Category.id_comp]

/-- 概要：指定零旗に向かう元の全旗実現の実収縮。
方針：既証の可縮性から Ex∞ 単位の零化を選ぶ。
規約：標的は同じ対象の関手的 Kan 模型。使われ方：後合成した零化。 -/
def closedKernelZeroFlagContraction {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    SSet.Homotopy
      (stdSimplex.isTerminalObj₀.from (closedKernelRealization P) ≫
        closedKernelZeroFlag P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedKernelRealization P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedKernelRealization P)) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (closedKernelRealization P)) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact Classical.choice (specifiedPoint_map_homotopy (closedKernelZeroFlag P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) (closedKernelRealization_toPoint_isIso P))

end SerrePositivity.KST.Fibration.Relative
