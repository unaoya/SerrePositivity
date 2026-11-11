module
public import SerrePositivity.KST.SConstruction.DGCochainZeroTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHomExt

/-! # 三つの実零 Hom から得る comma Hom の零性
概要：両成分 Hom と比較標的が実零なら、元の comma Hom 複体自体が実零となる。
方針：同じ恒等鎖写像と零射を、二射影と比較 cochain で判定する。
規約：実複体の零性を証明する。使われ方：指定二軸間の半直交性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)

/-- 元の三つの Hom が実零なら、同じ comma Hom 複体も実零対象。 -/
lemma dgCommaHom_isZero
    (hA : IsZero (homObject R C X.source Y.source))
    (hB : IsZero (homObject R E X.replacement Y.replacement))
    (hT : IsZero (homObject R E X.replacement (F.obj Y.source))) :
    IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R C E F X Y
  · exact hA.eq_of_tgt _ _
  · exact hB.eq_of_tgt _ _
  · exact (dgCochain_eq_zero_of_isZero_target hT (-1) _).trans
      (dgCochain_eq_zero_of_isZero_target hT (-1) _).symm

end SerrePositivity.KST.SConstruction
