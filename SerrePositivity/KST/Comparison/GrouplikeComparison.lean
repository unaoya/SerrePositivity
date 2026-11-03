module

public import SerrePositivity.KST.Comparison.GroupCompletionPathIdentity
public import SerrePositivity.KST.Comparison.RegularBarHomotopyFiber
public import SerrePositivity.KST.Comparison.AlternativeFiberCriterion

/-!
# 群状単体的モノイドの標準群完備化写像の比較

概要：群状単体的モノイドから Kan 置換した bar のループ空間への標準写像は局所化同型。
方針：正則 bar のホモトピーファイバーを path の厳密なファイバーと比較し、既存の標準写像との一致を使う。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の群状モノイドの比較部分。
各単体次数で群であることやモノイドの Kan 性を仮定しない。
使われ方：BĜL のホモトピー群の比較と plus 構成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：群状単体的モノイドの標準群完備化写像は anodyne 局所化同型。
方針：正則 bar 束と path fibration の全空間を局所化同型で比較し、基点上の実際の loop の引き戻しで判定する。
規約：Segal 1974 Proposition 1.5。KST Lemma 2.13 の分類空間の比較の根幹。
使われ方：ĜL の delooping と高次ホモトピー群の次数移動。
-/
theorem monoidGroupCompletionMap_localized_isIso (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidGroupCompletionMap M)) := by
  let Y := monoidBarKanPointed M
  let p := (Spectra.pathEndpoint Y).right
  let b := SSet.const (X := ⊤_ SSet.{u}) Y.basepoint
  have hpb := loopPathRestriction_isPullback Y
  let sq : CommSq (monoidGroupCompletionMap M ≫ loopPathRestriction Y)
      (terminal.from (monoidSpace M)) p b := ⟨by
    rw [Category.assoc, hpb.w, ← Category.assoc]
    congr 1
    exact terminalIsTerminal.hom_ext _ _⟩
  let : IsIso (terminal.from (Δ[0] : SSet.{u})) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀.{u} terminalIsTerminal _
  have hs : IsHomotopyPullback sq := by
    apply (isHomotopyPullback_iff_of_localized_isIso
      (regularBarFiber_isPullback M).toCommSq sq
      (𝟙 _) (regularBarPathMap M) (terminal.from (Δ[0] : SSet.{u}))
      (AnodyneKanReplacement.unit.app (monoidBar M)) ?_ ?_ ?_ ?_
      (by infer_instance) (regularBarPathMap_localized_isIso M) (by infer_instance)
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
        (AnodyneKanReplacement.unit_anodyne (monoidBar M)))).mp
      (regularBarFiber_homotopyPullback M hG)
    · rw [Category.id_comp]
      exact (monoidGroupCompletionMap_path M).symm
    · exact terminalIsTerminal.hom_ext _ _
    · exact (regularBarPathMap_endpoint M).symm
    · rw [SSet.yonedaEquiv_symm_zero, SSet.const_comp, SSet.comp_const]
      simp only [Y, monoidBarKanPointed, PointedSimplicialSet.basepoint_ofVertex]
      rfl
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance
  apply (isHomotopyPullback_iff_alternative_fiber sq (𝟙 _) (by infer_instance)
    p hp (Category.id_comp p) hpb.flip (monoidGroupCompletionMap M)
    (terminalIsTerminal.hom_ext _ _) (by simp)).mp hs

end SerrePositivity.KST.Comparison
