module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationAdjunctionDescent
public import SerrePositivity.KST.LocalizingInvariants.PointInitialAdjunction

/-!
概要：任意の辺集合の局所化射は、元の始対象の頂点を始対象へ送る。
方針：点からの実左随伴を局所化に沿って下ろし、元の写像空間の可縮性へ戻す。
規約：商の始対象性は結論として導く。使われ方：商の pointed 性と真の核。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma localization_preservesInitial {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : IsLocalization F W)
    (x : X _⦋0⦌) (hx : IsInitialVertex x) :
    IsInitialVertex (F.app (Opposite.op ⦋0⦌) x) := by
  let H : Q ⟶ (Δ[0] : SSet.{u}) := SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  let a := initialPointAdjunction (F ≫ H) x hx
  let d := localizationAdjunctionDescent (SSet.const x) F H W hF a
  have h := pointAdjunction_isInitial d (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  change IsInitialVertex (F.app (Opposite.op ⦋0⦌) (PinchedHom.constant x 0)) at h
  rw [pinchedConstant_zero] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants
