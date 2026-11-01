module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomAugmentedClosedFamily
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.ExtensionRepresentableClosedNaturality
/-!
概要：同時に持ち上げた閉射を、実延長した代表加群間の同じ閉射へ比較する。
方針：代表延長同型の自然性と閉射族の厳密な評価式を合成する。
規約：端点には元の代表延長同型を使い、元の閉射を別の射へ置き換えない。
使われ方：c′ の cone 精密化の代表加群の場合の第一辺比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] [Small.{u} D]
  (value : Set.Iio a → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (source target : K → Set.Iio a)
  (f : ∀ k, ForgetEnrichment.of (Complex R) (value (source k)) ⟶
    ForgetEnrichment.of (Complex R) (value (target k)))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

local notation "C" => (DGCategoryPresentationCode.Objects R κ (dgClosedFamilySourceCode R κ c a D value F source target f hκ hK))
local notation "L" => dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK
local notation "g" => dgClosedFamilySourceArrow R κ c a D value F source target f hκ hK

lemma dgClosedFamilySourceRepresentableArrow_comm (k : K) :
    (dgModuleExtension R C D L).onClosed.map ((dgYoneda R C).onClosed.map (g k)) ≫
      (dgModuleExtensionRepresentableIso R C D L (target k)).hom =
    (dgModuleExtensionRepresentableIso R C D L (source k)).hom ≫
      (dgYoneda R D).onClosed.map (f k) := by
  have h := dgModuleExtensionRepresentableIso_closed_naturality R C D L (g k)
  rw [dgClosedFamilySourceArrow_map] at h
  exact h

end SerrePositivity.DifferentialGraded
