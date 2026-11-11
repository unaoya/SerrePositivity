module
public import SerrePositivity.KST.SConstruction.DGGluingAxesCoconeInclusion
public import SerrePositivity.KST.SConstruction.DGGluingAxesCoconeProjection

/-! # 元の二軸列の全 Hom 短完全性
概要：任意の実試験対象から見た元の二軸列は、鎖複体の短完全列となる。
方針：同じ二つの後合成射を標準二成分 cocone の短完全列へ同型で移す。
規約：零成分・二射・第三 cochain を保持。使われ方：実 Yoneda 円錐比較の準同型性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "f" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T
  (dgGluingRightAxisObject R C D M zc X.right) X
  (dgGluingAxisRightInclusion R C D M zc hc X)
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T X
  (dgGluingLeftAxisObject R C D M zd X.left)
  (dgGluingAxisLeftProjection R C D M zd hd X)

/-- 元の二軸射による全 Hom 後合成の合成は厳密に零。 -/
lemma dgGluingAxesHom_comp_zero : f ≫ g = 0 := by
  apply (cancel_mono (dgGluingToLeftAxisHomIso R C D M zd hd T X.left).hom).mp
  rw [Category.assoc, dgGluingAxisLeftProjection_postcompose_hom,
    dgGluingAxisRightInclusion_post_left, zero_comp]

/-- 元の試験対象・二軸射を保持した、鎖複体の実短複体。 -/
def dgGluingAxesHomShortComplex : ShortComplex (Complex R) :=
  ShortComplex.mk f g (dgGluingAxesHom_comp_zero R C D M zc hc zd hd T X)

/-- 同じ実短複体は、標準二成分 cocone の元の短複体と実同型。 -/
def dgGluingAxesHomShortComplexIso : dgGluingAxesHomShortComplex R C D M zc hc zd hd T X ≅
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X) :=
  ShortComplex.isoMk (dgGluingRightAxisHomCoconeIso R C D M zc hc T X)
    (dgGluingHomBiprodCoconeIso R C D M T X)
    (dgGluingToLeftAxisHomIso R C D M zd hd T X.left)
    (dgGluingAxesCoconeInclusion_square R C D M zc hc T X).symm
    (dgGluingAxesCoconeProjection_square R C D M zd hd T X).symm

/-- 元の二軸列の全 Hom 複体は、追加仮定なしに短完全。 -/
lemma dgGluingAxesHomShortComplex_shortExact :
    (dgGluingAxesHomShortComplex R C D M zc hc zd hd T X).ShortExact :=
  ShortComplex.shortExact_of_iso (dgGluingAxesHomShortComplexIso R C D M zc hc zd hd T X).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex_shortExact _ _)

/-- 同じ元の二射による円錐比較は、全試験対象に対して実準同型となる。 -/
lemma dgGluingAxesHomConeComparison_quasiIso :
    QuasiIso (complexConeDesc f g (dgGluingAxesHom_comp_zero R C D M zc hc zd hd T X)) := by
  change QuasiIso (mappingCone.descShortComplex
    (dgGluingAxesHomShortComplex R C D M zc hc zd hd T X))
  exact mappingCone.quasiIso_descShortComplex
    (dgGluingAxesHomShortComplex_shortExact R C D M zc hc zd hd T X)

end SerrePositivity.KST.SConstruction
