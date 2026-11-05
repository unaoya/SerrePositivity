module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProductMap
public import SerrePositivity.InfinityCategories.Stable.Exact.FiberSquareRightTransport

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
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

lemma exists_laxQuotientProductFiber :
    ∃ s : FiberSquare (X := Sp.{u})
        (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).toTruncated,
      ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj Sp.{u}))
        (functorVertex s.square) (functorVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square),
        IsInvertibleEdge l ∧ ((pre squareRightEdge).app Sp.{u}).app (Opposite.op ⦋1⦌) l.edge =
          ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso hΦ) p q i r h).edge.edge := by
  let g : (Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
    SSet.yonedaEquiv.symm (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).edge
  obtain ⟨s, l, hi, hl⟩ := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exists_fiberSquare_right_transport (X := Sp.{u})
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)) ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle_isFiber p q i r h hΦ))
    g ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso hΦ) p q i r h)
  let s' : FiberSquare (X := Sp.{u})
      (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).toTruncated := {
    square := s.square
    zero_corner := s.zero_corner
    right_edge := s.right_edge.trans (SSet.yonedaEquiv.symm_apply_apply g)
    isPullback := s.isPullback }
  exact ⟨s', l, hi, hl⟩

def laxQuotientProductFiberSquare : FiberSquare (X := Sp.{u})
    (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).toTruncated :=
  Classical.choose (hΦ.exists_laxQuotientProductFiber p q i r h)

def laxQuotientProductFiberEdge : Truncated.Edge
    (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj Sp.{u}))
    (functorVertex (hΦ.laxQuotientProductFiberSquare p q i r h).square)
    (functorVertex ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square) :=
  Classical.choose (Classical.choose_spec (hΦ.exists_laxQuotientProductFiber p q i r h))

lemma laxQuotientProductFiberEdge_isInvertible :
    IsInvertibleEdge (hΦ.laxQuotientProductFiberEdge p q i r h) :=
  (Classical.choose_spec
    (Classical.choose_spec (hΦ.exists_laxQuotientProductFiber p q i r h))).1

lemma laxQuotientProductFiberEdge_right :
    ((pre squareRightEdge).app Sp.{u}).app (Opposite.op ⦋1⦌)
        (hΦ.laxQuotientProductFiberEdge p q i r h).edge =
      ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso hΦ) p q i r h).edge.edge :=
  (Classical.choose_spec
    (Classical.choose_spec (hΦ.exists_laxQuotientProductFiber p q i r h))).2

def laxQuotientProductFiberComparison : FunctorIso
    (hΦ.laxQuotientProductFiberSquare p q i r h).square
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (hΦ.laxQuotientProductFiberEdge p q i r h)) :=
    hΦ.laxQuotientProductFiberEdge_isInvertible p q i r h
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (hΦ.laxQuotientProductFiberEdge p q i r h))

lemma laxQuotientProductFiber_isFiber :
    IsFiberSequence (hΦ.laxQuotientProductFiberSquare p q i r h).toZeroTriangle :=
  (hΦ.laxQuotientProductFiberSquare p q i r h).isPullback

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
