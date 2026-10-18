module

public import SerrePositivity.KST.DerivedGeometry.LinearYonedaShift
public import SerrePositivity.KST.DerivedGeometry.LinearComplexHomotopy
public import SerrePositivity.DifferentialGraded.Module.Pretriangulated

/-!
概要：複体の代表加群の関手を Mathlib のホモトピー圏から降ろす。
方針：実際の dg Yoneda が境界を保つことを、閉零射の比較を通して使う。
規約：元の chain homotopy を全 dg 自然な加群ホモトピーへ送る。
使われ方：Drinfeld §2.4、KST D4・§10-7 の三角構造の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：複体のホモトピックな射は代表加群のホモトピー圏で等しい。
方針：閉零射へ戻し、dg Yoneda の境界保存を適用する。
規約：評価ごとの独立なホモトピーを代用しない。
使われ方：Drinfeld §2.4、KST D4 の実際のホモトピー圏からの比較。
-/
theorem complexYoneda_preservesHomotopy {X Y : CochainComplex C ℤ} {f g : X ⟶ Y}
    (h : Homotopy f g) :
    (moduleToHomotopy A (CochainComplex C ℤ)).map (representablePostcompose A f) =
      (moduleToHomotopy A (CochainComplex C ℤ)).map (representablePostcompose A g) := by
  let f' := (closedHomEquiv A X Y).symm f
  let g' := (closedHomEquiv A X Y).symm g
  have hb : boundaryRelation A (CochainComplex C ℤ) f' g' :=
    (boundary_iff A _ _ f' g').mpr (by
      change Nonempty (Homotopy (closedHomEquiv A X Y f') (closedHomEquiv A X Y g'))
      simpa only [f', g', Equiv.apply_symm_apply] using (show Nonempty (Homotopy f g) from ⟨h⟩))
  rw [representablePostcompose_eq_yoneda, representablePostcompose_eq_yoneda]
  exact (toHomotopy_map_eq_iff A (RightModule A (CochainComplex C ℤ)) _ _).mpr
    ((dgYoneda A (CochainComplex C ℤ)).preserves_boundary f' g' hb)

/--
概要：実際の複体のホモトピー圏から dg 加群のホモトピー圏への代表加群関手。
方針：具体的な代表加群関手を chain homotopy の合同関係で降ろす。
規約：既存の二つのホモトピー商を使う。
使われ方：Drinfeld §2.4、KST D4 の三角構造と acyclic 局所化。
-/
def nativeHomotopyYoneda : _root_.HomotopyCategory C (.up ℤ) ⥤
    ModuleHomotopyCategory A (CochainComplex C ℤ) :=
  CategoryTheory.Quotient.lift (homotopic C (.up ℤ))
    (complexYoneda A ⋙ moduleToHomotopy A (CochainComplex C ℤ))
    (by intro X Y f g h; exact complexYoneda_preservesHomotopy A h.some)

/--
概要：ホモトピー圏への代表加群関手は整数 shift と整合的に可換。
方針：証明済みの shift 構造を既存の商への降下に渡す。
規約：比較同型を商の後で選び直さない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の標準三角形の比較。
-/
instance nativeHomotopyYoneda_commShift : (nativeHomotopyYoneda (C := C) A).CommShift ℤ :=
  Quotient.liftCommShift _ _ _ _

/--
概要：ホモトピー圏へ降ろした代表加群関手と元の関手の比較正方形。
方針：既存の合同関係による商の因子分解同型を使う。
規約：元の具体的な chain map の像を固定する。
使われ方：Drinfeld §2.4、KST D4 の標準 cone 三角形の比較。
-/
def nativeHomotopyYonedaFacIso :
    _root_.HomotopyCategory.quotient C (.up ℤ) ⋙ nativeHomotopyYoneda A ≅
      complexYoneda A ⋙ moduleToHomotopy A (CochainComplex C ℤ) := by
  unfold nativeHomotopyYoneda
  exact CategoryTheory.Quotient.lift.isLift _ _ _

/--
概要：ホモトピー圏へ降ろした関手の比較正方形は shift と整合的。
方針：商の shift 構造の既存の互換性を使う。
規約：因子分解同型を取り替えない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の三角形の比較正方形。
-/
instance nativeHomotopyYonedaFacIso_commShift :
    NatTrans.CommShift (nativeHomotopyYonedaFacIso (C := C) A).hom ℤ := by
  unfold nativeHomotopyYonedaFacIso nativeHomotopyYoneda
  apply CategoryTheory.Quotient.liftCommShift_compatibility

end SerrePositivity.KST.DerivedGeometry.LinearComplex
