module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：正則 pairing のホーンセル分解による Kan 複体への延長。
方針：全ホーンの持ち上げ性を coproduct・pushout・超限合成で保ち、pairing のセル分解へ適用する。
規約：モデル構造の弱同値や因子分解を使わず、持ち上げ性の閉包だけを使う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の反転比較の有限な延長領域。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits HomotopicalAlgebra SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：正則 pairing を持つ部分複体の包含は全ホーンを持ち上げる射に対して持ち上げ性を持つ。
方針：pairing の相対セル分解の各セルで仮定を使い、左持ち上げ性の閉包で合成する。
規約：対象や射にはモデル構造の性質を仮定しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーン充填から領域全体の延長を得る一般補題。 -/
lemma regularPairing_hasLiftingProperty {X E B : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] (p : E ⟶ B)
    (h : ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty (horn (n + 1) i).ι p) :
    HasLiftingProperty A.ι p := by
  let W : MorphismProperty SSet.{u} := (MorphismProperty.ofHoms (fun _ : Unit ↦ p)).llp
  have hW : W A.ι := by
    exact transfiniteCompositionsOfShape_le _ _ _
      ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
        refine (?_ : (_ : MorphismProperty _) ≤ W) _
          (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
        simp only [pushouts_le_iff, coproducts_le_iff]
        rintro _ _ _ ⟨c⟩
        intro U V q hq
        cases hq with
        | mk i => exact h c.dim c.index⟩
  exact hW p ⟨()⟩

/-- 概要：正則 pairing を持つ部分複体上の Kan 値図式は全体へ延長する。
方針：Kan のホーン充填から終対象への射の持ち上げ性を得て、正則 pairing の一般補題を使う。
規約：延長は元の部分複体上で厳密に一致する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の両端射影の充填を構成する。 -/
lemma exists_extension_of_regularPairing {X K : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [KanComplex K] (f : (A : SSet.{u}) ⟶ K) :
    ∃ F : X ⟶ K, A.ι ≫ F = f := by
  have h : ∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (horn (n + 1) i).ι (terminal.from K) := by
    intro n i
    constructor
    intro a b sq
    obtain ⟨l, hl⟩ := KanComplex.hornFilling a
    exact CommSq.HasLift.mk' { l := l, fac_left := hl.symm, fac_right := terminal.hom_ext _ _ }
  have := regularPairing_hasLiftingProperty P (terminal.from K) h
  let sq : CommSq f A.ι (terminal.from K) (terminal.from X) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
