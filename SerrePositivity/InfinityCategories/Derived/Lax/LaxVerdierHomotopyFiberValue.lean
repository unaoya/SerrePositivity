module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProductFiberVertices
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare

/-!
概要：元の E(A) を、実積から E(Q) への BF 射の実 homotopyFiber と同定する。
方針：同じ右辺の二つの fiber 四角形の全図式同型を用いて左下の同値を回収する。
規約：群の同型の寄せ集めではない。使われ方：d8 の実 fiber 模型と値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance homotopyFiberValueSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homotopyFiberValueSquareQuasicategory :
    Quasicategory (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) := F2.quasicategory_tensor _ _
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def laxQuotientProductFiberBFComparison : FunctorIso
    (hΦ.laxQuotientProductFiberSquare p q i r h).square
    (FiberModel.homotopyFiberSquare (hΦ.laxQuotientProductMap p q r)).square :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.nonempty_functorIso (X := Sp.{u})
    (hΦ.laxQuotientProductFiberSquare p q i r h)
    (FiberModel.homotopyFiberSquare (hΦ.laxQuotientProductMap p q r)))

def laxQuotientHomotopyFiberValueIso :
    SpectrumHo.obj (OmegaSpectrum.homotopyFiber (hΦ.laxQuotientProductMap p q r)) ≅
      SpectrumHo.obj (value Φ A) :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk
    (FiberModel.homotopyFiberSquare_vertex (hΦ.laxQuotientProductMap p q r)))).symm ≪≫
      (FunctorIso.app (hΦ.laxQuotientProductFiberBFComparison p q i r h)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).symm ≪≫
          hΦ.laxQuotientProductFiberLeftIso p q i r h

end SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.homotopyFiberValueSimplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.homotopyFiberValueSimplicialCategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.homotopyFiberValueSimplicialCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.homotopyFiberValueSquareQuasicategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.homotopyFiberValueSquareQuasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberBFComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberBFComparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberBFComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientHomotopyFiberValueIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberBFComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberBFComparison._proof_1
