module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.PairingRegular
public import SerrePositivity.InfinityCategories.F1.Simplicial.StandardSimplexInnerFaceIndex
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
概要：twisted arrow の延長領域の pairing は inner であり、包含は inner anodyne。
方針：有限頂点集合の挿入点の前後の頂点を一意な面の番号の両端不在へ移す。
規約：left fibration 性のホーンの重みとの接合は後続の工程。
使われ方：twisted arrow 射影の left fibration 性を支える組み合わせ論の延長定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- pairing の実際の余次元一の面の番号は両端ではない。 -/
lemma twistedArrowExtensionPairing_innerIndex {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s : (twistedArrowExtensionPairing.{u} i hi).II) :
    ((twistedArrowExtensionPairing i hi).isUniquelyCodimOneFace s).index rfl ≠ 0 ∧
      ((twistedArrowExtensionPairing i hi).isUniquelyCodimOneFace s).index rfl ≠
        Fin.last (s.val.dim + 1) := by
  exact stdSimplexUniqueFace_innerIndex s.val.toN
    ((twistedArrowExtensionPairing i hi).p s).val.toN
    ((twistedArrowExtensionPairing i hi).isUniquelyCodimOneFace s)
    (twistedArrowSupportPivot i (stdSimplexNondegenerateSupport s.val.toN))
    (twistedArrowExtensionPairing_support i hi s)
    (twistedArrowSupportPivot_interior i hi _
      ((twistedArrowOutsideSimplexEquiv i) s.val).property)

/-- 正則 pairing は inner horn だけを接合する。 -/
instance twistedArrowExtensionPairing_isInner {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) : (twistedArrowExtensionPairing.{u} i hi).IsInner where
  ne_zero s d hd := by
    subst d
    exact (twistedArrowExtensionPairing_innerIndex i hi s).1
  ne_last s d hd := by
    subst d
    exact (twistedArrowExtensionPairing_innerIndex i hi s).2

/-- 左ホーンの twisted arrow の延長領域の包含は inner anodyne。 -/
lemma twistedArrowExtensionDomain_innerAnodyne {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) : innerAnodyneExtensions (twistedArrowExtensionDomain.{u} n i).ι :=
  (twistedArrowExtensionPairing i hi).innerAnodyneExtensions

end SerrePositivity.InfinityCategories
