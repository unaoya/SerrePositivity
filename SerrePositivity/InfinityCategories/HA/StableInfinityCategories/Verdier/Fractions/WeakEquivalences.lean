module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingBaseChange

/-! # Verdier 列の Waldhausen 弱同値

cofiber が包含の本質像に属する実辺を使う。商の核条件から本質像が既に
安定閉包であることを証明し、実二単体の二対三性と実押し出しの安定性を得る。
厚さの追加条件や商の冪等完備化はこの工程には不要である。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration

/-- 選択に依存しない、包含の本質像に cofiber を持つ実辺。 -/
def weakEquivalences {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    Set (B.obj _⦋1⦌) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 商の核は零・同型・cofiber・fiber で閉じている。 -/
lemma stableClosure_essentialImage (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) x} = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i := by
  ext x
  exact ⟨fun hx => (h.kernel x).1
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)
      (fun y hy => (h.kernel y).2 hy) hx), _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem⟩

/-- 指定した cofiber で W 所属を判定できる。 -/
lemma mem_weakEquivalences_iff (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {x y : B.obj _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj B.obj) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) :
    f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ↔ s.cofiber ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i := by
  have hs := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) s
  change f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) z} ↔
    s.cofiber ∈ {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) z} at hs
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage h] at hs
  exact hs

/-- W は商で可逆となる実辺のクラスに等しい。 -/
lemma mem_weakEquivalences_iff_invertible (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {x y : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) x y) :
    f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f.map ((truncation 2).map q.hom)) := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff h s, ← h.kernel s.cofiber]
  exact (s.map_isInvertible_iff_zero q.hom).symm

/-- 実合成二単体を保つ二対三性。 -/
theorem weakEquivalences_twoOfThree (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (τ : Δ[2] ⟶ B.obj) :
    let W := fun j : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ j ≫ τ) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage h] using
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_twoOfThree (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) τ

/-- 実押し出しに沿って W 所属は保存され、反映される。 -/
theorem weakEquivalences_pushout_iff (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (L : Δ[1] ⊗ Δ[1] ⟶ B.obj) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage h] using
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_pushout_iff (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) L hL

/-- 安定性による引き戻し版。 -/
theorem weakEquivalences_pullback_iff (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (L : Δ[1] ⊗ Δ[1] ⟶ B.obj) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage h] using
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_pullback_iff (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) L hL

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.mem_weakEquivalences_iff := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.mem_weakEquivalences_iff_invertible := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.stableClosure_essentialImage := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakEquivalences := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakEquivalences_pullback_iff := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pullback_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakEquivalences_pushout_iff := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pushout_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakEquivalences_twoOfThree := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_twoOfThree

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakEquivalences.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences.eq_1
