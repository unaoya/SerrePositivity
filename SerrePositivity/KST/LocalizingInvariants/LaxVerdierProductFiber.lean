module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierProductMap
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FiberSquareRightTransport

/-!
概要：中項を元の実積、右辺を元の BF 商射とする d8 の実 fiber 四角形。
方針：指定右辺の関手同型を全四角形の可逆辺に持ち上げ、その同じ辺と制限を保存する。
規約：fiber 性は構成から証明する。使われ方：実 pullback 比較に必要な product fiber。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productFiberSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance productFiberNerveQuasicategory : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

lemma exists_laxQuotientProductFiber :
    ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare (X := Sp.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).toTruncated,
      ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj Sp.{u}))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge l ∧ ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app Sp.{u}).app (Opposite.op ⦋1⦌) l.edge =
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso hΦ) p q i r h).edge.edge := by
  let g : (Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).edge
  obtain ⟨s, l, hi, hl⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exists_fiberSquare_right_transport (X := Sp.{u})
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle_isFiber p q i r h hΦ))
    g ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso hΦ) p q i r h)
  let s' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare (X := Sp.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).toTruncated := {
    square := s.square
    zero_corner := s.zero_corner
    right_edge := s.right_edge.trans (SSet.yonedaEquiv.symm_apply_apply g)
    isPullback := s.isPullback }
  exact ⟨s', l, hi, hl⟩

def laxQuotientProductFiberSquare : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare (X := Sp.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).toTruncated :=
  Classical.choose (hΦ.exists_laxQuotientProductFiber p q i r h)

def laxQuotientProductFiberEdge : Truncated.Edge
    (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj Sp.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square) :=
  Classical.choose (Classical.choose_spec (hΦ.exists_laxQuotientProductFiber p q i r h))

lemma laxQuotientProductFiberEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (hΦ.laxQuotientProductFiberEdge p q i r h) :=
  (Classical.choose_spec
    (Classical.choose_spec (hΦ.exists_laxQuotientProductFiber p q i r h))).1

lemma laxQuotientProductFiberEdge_right :
    ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app Sp.{u}).app (Opposite.op ⦋1⦌)
        (hΦ.laxQuotientProductFiberEdge p q i r h).edge =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso hΦ) p q i r h).edge.edge :=
  (Classical.choose_spec
    (Classical.choose_spec (hΦ.exists_laxQuotientProductFiber p q i r h))).2

def laxQuotientProductFiberComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (hΦ.laxQuotientProductFiberSquare p q i r h).square
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (hΦ.laxQuotientProductFiberEdge p q i r h)) :=
    hΦ.laxQuotientProductFiberEdge_isInvertible p q i r h
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (hΦ.laxQuotientProductFiberEdge p q i r h))

lemma laxQuotientProductFiber_isFiber :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hΦ.laxQuotientProductFiberSquare p q i r h).toZeroTriangle :=
  (hΦ.laxQuotientProductFiberSquare p q i r h).isPullback

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Eq (15)" (partial := stronger-hyp) "仮定：小安定圏で同じ Verdier 列を与え、Sp 値の弱局所化型関手を取る（Lean が強い：Ind の切除性から得る列を直接入力）。結論：二つの脚の値の直和を中央とする実ファイバー列と、その包含・差の射の同定（原典の同じ射の Sp 版）。"] _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiber_isFiber
