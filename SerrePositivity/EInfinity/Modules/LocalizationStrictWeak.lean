module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.SimplicialLocalization.SourceHom

/-!
# 元の弱射の同じ局所化辺の可逆性

概要：HTT §1.2.4 の意味で、指定された弱射の実局所化辺が可逆である。
方針：元の源の反転性と同じ生成射の自然性を、頂点の比較同型で結ぶ。
規約：可逆な別の辺を選んで元の辺と取り替えない。
使われ方：HA §4.2.3 の同じ全加群族の弱 Cartesian lift の反転。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.EInfinity SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations
open scoped Simplicial
variable (C : RelativeCategory.{u}) {X Y : C.category}

set_option maxHeartbeats 800000 in
-- 同じ局所化源の選択逆を含む二つの辺の型照合に計算を使う。
/-- 概要：指定された弱射の同じ局所化生成辺は可逆（HTT §1.2.4）。
方針：元の源での反転を、指定生成射の自然性の四角形で共役する。
規約：辺そのものの可逆性。使われ方：全加群族の弱 lift の native な反転。 -/
lemma localizationStrictEdge_invertible_of_weak (f : X ⟶ Y) (hf : C.weakEquivalences f) :
    IsInvertibleEdge (coherentNerveEdge (kanLocalizationStrictHom C f)).toTruncated := by
  have hw := localizationNerveSourceMap_inverts C
    (show ComposableArrows.mk₁ f ∈ weakNerveEdges C from ⟨X, Y, f, hf, rfl⟩)
  change IsInvertibleEdge (X := localizationNerve C) ((edgeOfSimplex (ComposableArrows.mk₁ f)).map
    ((truncation 2).map (localizationNerveSourceMap C))) at hw
  have he : IsInvertibleEdge (X := localizationNerve C)
      ((nerve.edgeMk f).map (localizationNerveSourceMap C)).toTruncated := by
    exact (isInvertibleEdge_congr (X := localizationNerve C)
      (e := (edgeOfSimplex (ComposableArrows.mk₁ f)).map
        ((truncation 2).map (localizationNerveSourceMap C)))
      (f := ((nerve.edgeMk f).map (localizationNerveSourceMap C)).toTruncated) rfl).mp hw
  let m := (hoFunctor.map (localizationNerveSourceMap C)).toFunctor.map
    (SSet.HomotopyCategory.homMk (nerve.edgeMk f))
  have : IsIso m := he
  have hn := localizationStrictSourceIso_naturality C f
  have h : SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C f)) =
      (localizationStrictSourceIso C X).inv ≫ m ≫ (localizationStrictSourceIso C Y).hom := by
    calc
      _ = (localizationStrictSourceIso C X).inv ≫
          ((localizationStrictSourceIso C X).hom ≫
            SSet.HomotopyCategory.homMk
              (coherentNerveEdge (kanLocalizationStrictHom C f))) := by simp
      _ = (localizationStrictSourceIso C X).inv ≫ (m ≫ (localizationStrictSourceIso C Y).hom) := by
        rw [← hn]
      _ = _ := by rfl
  change IsIso (SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C f)))
  rw [h]
  infer_instance

attribute [cite HTT "1.2.4" (partial := component)
  "同じ相対局所化の指定弱射の生成辺に限り、ホモトピー圏の可逆性を示す。"]
  localizationStrictEdge_invertible_of_weak

end SerrePositivity.EInfinity.Modules
