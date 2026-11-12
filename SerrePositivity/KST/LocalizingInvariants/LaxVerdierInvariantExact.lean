module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierInvariantFiber

/-!
概要：仮定付き lax Verdier 列の元の包含・商に対する全整数長完全列。
方針：実 fiber 列と元の値の群を保つ K-5 の比較を同じ入力へ適用する。
規約：Q の抽象構成は要求しない。使われ方：d8 の値と後続の pro fiber 列の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def laxQuotientConnecting (j : ℤ) : valueHomotopyGroup Φ Q (j + 1) →*
    valueHomotopyGroup Φ A j := hΦ.connecting (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h) j

include hΦ h in
lemma laxQuotient_exact_middle (j : ℤ) (x : valueHomotopyGroup Φ (laxCategory p q) j) :
    valueHomotopyMap Φ r j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ A j, valueHomotopyMap Φ i j z = x :=
  hΦ.exact_middle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h) j x

lemma laxQuotient_exact_left (j : ℤ) (x : valueHomotopyGroup Φ A j) :
    valueHomotopyMap Φ i j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ Q (j + 1), hΦ.laxQuotientConnecting p q i r h j z = x :=
  hΦ.exact_left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h) j x

lemma laxQuotient_exact_right (j : ℤ) (x : valueHomotopyGroup Φ Q (j + 1)) :
    hΦ.laxQuotientConnecting p q i r h j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ (laxCategory p q) (j + 1),
        valueHomotopyMap Φ r (j + 1) z = x :=
  hΦ.exact_right (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h) j x

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
