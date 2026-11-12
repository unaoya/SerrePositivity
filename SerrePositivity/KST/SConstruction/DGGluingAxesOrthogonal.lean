module
public import SerrePositivity.KST.SConstruction.DGGluingLeftAxis
public import SerrePositivity.KST.SConstruction.DGGluingRightAxis
public import SerrePositivity.KST.SConstruction.DGCommaHomZero

/-! # 指定した実二軸間の半直交 Hom の零性
概要：元の右軸から左軸への全 Hom 複体は、指定閉零対象により実零となる。
方針：代表加群 comma 表示の三つの Hom 零性を使い、元の実 Hom 同型で戻す。
規約：順序は Map(D,C)=0。使われ方：二軸分解から商の生成性への接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))

include hc hd in
/-- 指定した同じ実右軸から実左軸への全 Hom 複体は実零対象。 -/
lemma dgGluingAxes_right_left_hom_isZero (d : D) (c : C) :
    IsZero (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (dgGluingRightAxisObject R C D M zc d) (dgGluingLeftAxisObject R C D M zd c)) :=
  (dgCommaHom_isZero R D (RightModule R C) M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingRightAxisObject R C D M zc d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (dgGluingLeftAxisObject R C D M zd c))
    (dgHom_isZero_of_closed_zero_target R zd hd d)
    (dgRepresentableClosedZeroHom R zc hc (representable R c))
    (dgRepresentableClosedZeroHom R zc hc (M.rightAt zd))).of_iso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M
        (dgGluingRightAxisObject R C D M zc d) (dgGluingLeftAxisObject R C D M zd c))

end SerrePositivity.KST.SConstruction
