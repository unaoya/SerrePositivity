module

public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiberVertices
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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance homotopyFiberValueSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homotopyFiberValueSquareQuasicategory :
    Quasicategory (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) := F2.quasicategory_tensor _ _
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def laxQuotientProductFiberBFComparison : FunctorIso
    (hΦ.laxQuotientProductFiberSquare p q i r h).square
    (FiberModel.homotopyFiberSquare (hΦ.laxQuotientProductMap p q r)).square :=
  Classical.choice (FiberComparison.nonempty_functorIso (X := Sp.{u})
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

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
