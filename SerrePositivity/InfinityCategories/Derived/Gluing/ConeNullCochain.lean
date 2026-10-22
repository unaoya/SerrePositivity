module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeBoundary

/-! 指定した kernel の零ホモトピー cochain を、同じ代表射と Hom 逆同型で native 側へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "i" => dgGluingConeInr R C D M Y Z f p q
local notation "ki" => dgGluingKernelConeInr R C D M Y Z f
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q
local notation "kf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgGluingToKernelComma R C D M)) f
local notation "post" => dgGluingKernelConeRepresentativePost R C D M Y Z f p q KY

/-- 元の指定 cochain を、同じ実後合成と native Hom の逆鎖同型で移す。 -/
def dgGluingConeNullCochain :
    Cochain (𝟙_ (Complex R)) (dgGluingHomComplex R C D M Y W) (-1) :=
  (dgGluingKernelConeNullCochain R C D M Y Z f).comp
    (Cochain.ofHom (post ≫ (dgGluingKernelHomIso R C D M Y W).inv)) (add_zero (-1))

/-- 移送した同じ cochain の境界は、native の元の射と同じ円錐包含の実合成。 -/
lemma dgGluingConeNullCochain_boundary :
    δ (-1) 0 (dgGluingConeNullCochain R C D M Y Z f p q) =
      Cochain.ofHom (ForgetEnrichment.homTo (Complex R) (f ≫ i)) := by
  have hm : (dgGluingToKernelComma R C D M).onClosed.map (f ≫ i) = (kf ≫ ki) ≫ a := by
    rw [CategoryTheory.Functor.map_comp, dgGluingConeInr_kernel, Category.assoc]
  have hp : ForgetEnrichment.homTo (Complex R) (kf ≫ ki) ≫ post =
      ForgetEnrichment.homTo (Complex R)
        ((dgGluingToKernelComma R C D M).onClosed.map (f ≫ i)) := by
    rw [hm]
    exact dgGluingClosed_postcompose R E (kf ≫ ki) a
  rw [dgGluingConeNullCochain, δ_comp_ofHom, dgGluingKernelConeNullCochain_boundary,
    ← Cochain.ofHom_comp, ← Category.assoc, hp]
  change Cochain.ofHom
    ((ForgetEnrichment.homTo (Complex R) (f ≫ i) ≫
      (dgGluingToKernelComma R C D M).map Y W) ≫
        (dgGluingKernelHomIso R C D M Y W).inv) = _
  rw [dgGluingToKernelComma_map, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
