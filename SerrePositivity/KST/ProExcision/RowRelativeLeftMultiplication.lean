module
public import SerrePositivity.KST.ProExcision.ColumnRowMultiplicationSquare
public import SerrePositivity.KST.ProExcision.ColumnRowRelativeIso

/-!
# 実行側相対項への指定元の左乗法

概要：行側相対加群の左乗法と列側右乗法を実比較で同定する。
方針：実単体的正方形を bar、H_*、像の商へ順に移す。
規約：KST Proposition 4.14、SW92 §1.2。零性を写像の定義に含めない。
使われ方：行側への低次相対零化の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite Comparison
open scoped Simplicial

/-- 概要：実 bar 同型は列の右乗法と行の左乗法に可換。
方針：実半直積の正方形と対角反転の自然性を合成する。
規約：SW92 §1.2。使われ方：実 H_* 正方形への移行。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineBarIso_multiplication
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n : ℕ) :
    monoidBarMap (simplicialActionProductMap
        (I.reverseOpposite.columnRightActionHom (MulOpposite.op a) n)) ≫
        (I.reverseOppositeAffineBarIso n).hom =
      (I.reverseOppositeAffineBarIso n).hom ≫
        SSet.opFunctor.map (monoidBarMap (I.rowAffineLeftMap a n)) := by
  change monoidBarMap _ ≫ (monoidBarMap (I.reverseOppositeAffineIso n).hom ≫
      (monoidBarReverseOppositeIso (I.rowAffine n)).hom) =
    (monoidBarMap (I.reverseOppositeAffineIso n).hom ≫
      (monoidBarReverseOppositeIso (I.rowAffine n)).hom) ≫ _
  rw [← Category.assoc, ← monoidBarMap_comp, I.reverseOppositeAffineIso_multiplication,
    monoidBarMap_comp, Category.assoc, monoidBarReverseOppositeIso_natural, ← Category.assoc]

/-- 概要：実 H_* 同型は列の右乗法と行の左乗法に可換。
方針：実 bar 正方形と実鎖反転の自然性を合成する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：相対商の実比較。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_multiplication
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    F.map (monoidBarMap (simplicialActionProductMap
        (I.reverseOpposite.columnRightActionHom (MulOpposite.op a) n))) ≫
        (I.reverseOppositeAffineHomologyIso n F hF).hom =
      (I.reverseOppositeAffineHomologyIso n F hF).hom ≫
        F.map (monoidBarMap (I.rowAffineLeftMap a n)) := by
  change F.map _ ≫ (F.map (I.reverseOppositeAffineBarIso n).hom ≫
      hF.reversalNatIso.hom.app (monoidBar (I.rowAffine n))) =
    (F.map (I.reverseOppositeAffineBarIso n).hom ≫
      hF.reversalNatIso.hom.app (monoidBar (I.rowAffine n))) ≫ _
  rw [← Category.assoc, ← F.map_comp, I.reverseOppositeAffineBarIso_multiplication,
    F.map_comp, Category.assoc]
  have hn := hF.reversalNatIso.hom.naturality (monoidBarMap (I.rowAffineLeftMap a n))
  change F.map (SSet.opFunctor.map (monoidBarMap (I.rowAffineLeftMap a n))) ≫ _ = _ at hn
  rw [hn, ← Category.assoc]

/-- 概要：行側相対加群の実左乗法写像。
方針：実半直積写像を H_* に写し、標準包含の像による商へ降ろす。
規約：SW92 §1.2、基底は恒等。使われ方：行側安定零化の有限成分。 -/
def NonUnitalSimplicialRing.relativeRowAffineLeftMap
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    I.relativeRowAffineModule n F ⟶ I.relativeRowAffineModule n F :=
  relativeModuleMap _ _ (𝟙 _) (F.map (monoidBarMap (I.rowAffineLeftMap a n))) (by
    rw [← F.map_comp, ← monoidBarMap_comp, I.rowAffineLeftMap_section, Category.id_comp])

/-- 概要：行側と列側の実相対同型は指定元の乗法と可換。
方針：相対商写像の合成則と実 H_* 正方形を使う。
規約：KST Proposition 4.14、SW92 §1.2。中心性はこの比較に不要。
使われ方：列側の零写像を行側の実写像へ移す。 -/
lemma NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso_multiplication
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    relativeBarMap F (I.reverseOpposite.columnRightActionHom (MulOpposite.op a) n) ≫
        (I.reverseOppositeRelativeAffineIso n F hF).hom =
      (I.reverseOppositeRelativeAffineIso n F hF).hom ≫ I.relativeRowAffineLeftMap a n F := by
  unfold relativeBarMap relativeRowAffineLeftMap reverseOppositeRelativeAffineIso relativeModuleIso
  rw [relativeModuleMap_comp, relativeModuleMap_comp]
  apply relativeModuleMap_eq_of_right_eq
  exact I.reverseOppositeAffineHomologyIso_multiplication a n F hF

end SerrePositivity.KST.ProExcision
