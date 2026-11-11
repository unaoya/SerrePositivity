module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeBoundary

/-! 指定した kernel の零ホモトピー cochain を、同じ代表射と Hom 逆同型で native 側へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr R C D M Y Z f p q
local notation "ki" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr R C D M Y Z f
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap R C D M Y Z f p q
local notation "kf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M)) f
local notation "post" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativePost R C D M Y Z f p q KY

/-- 元の指定 cochain を、同じ実後合成と native Hom の逆鎖同型で移す。 -/
def dgGluingConeNullCochain :
    Cochain (𝟙_ (Complex R)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M Y W) (-1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain R C D M Y Z f).comp
    (Cochain.ofHom (post ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M Y W).inv)) (add_zero (-1))

/-- 移送した同じ cochain の境界は、native の元の射と同じ円錐包含の実合成。 -/
lemma dgGluingConeNullCochain_boundary :
    δ (-1) 0 (dgGluingConeNullCochain R C D M Y Z f p q) =
      Cochain.ofHom (ForgetEnrichment.homTo (Complex R) (f ≫ i)) := by
  have hm : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map (f ≫ i) = (kf ≫ ki) ≫ a := by
    rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_kernel, Category.assoc]
  have hp : ForgetEnrichment.homTo (Complex R) (kf ≫ ki) ≫ post =
      ForgetEnrichment.homTo (Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map (f ≫ i)) := by
    rw [hm]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosed_postcompose R E (kf ≫ ki) a
  rw [dgGluingConeNullCochain, δ_comp_ofHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain_boundary,
    ← Cochain.ofHom_comp, ← Category.assoc, hp]
  change Cochain.ofHom
    ((ForgetEnrichment.homTo (Complex R) (f ≫ i) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).map Y W) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M Y W).inv) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
