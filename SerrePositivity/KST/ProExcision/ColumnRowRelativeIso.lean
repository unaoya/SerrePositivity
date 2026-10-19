module
public import SerrePositivity.KST.ProExcision.RowAffineSection
public import SerrePositivity.KST.ProExcision.RelativeModuleIso
public import SerrePositivity.KST.ProExcision.RelativeBar

/-!
# 行側相対 bar 項と反対係数の列側相対項の実同型

概要：基底と全空間の実同型を相対加群の実同型へ降ろす。
方針：標準包含の実可換性を bar、H_*、通常商の順に移す。
規約：KST Proposition 4.14、SW92 §1.2。H_* は既存の自然な複体模型だけを借用する。
使われ方：列側の実零化から行側の実零化を得る比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Comparison

/-- 概要：反対転置の実 bar 同型は標準包含と可換。
方針：実半直積の可換性と対角 bar の反転の自然性を合成する。
規約：SW92 §1.2。使われ方：実相対ホモロジー同型への降下。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineBarIso_section
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    monoidBarMap (simplicialActionProductSection (I.reverseOpposite.hatGLColumnAction n)) ≫
        (I.reverseOppositeAffineBarIso n).hom =
      (I.reverseOppositeHatGLBarIso n).hom ≫
        SSet.opFunctor.map (monoidBarMap (I.rowAffineSection n)) := by
  change monoidBarMap _ ≫ (monoidBarMap (I.reverseOppositeAffineIso n).hom ≫
      (monoidBarReverseOppositeIso (I.rowAffine n)).hom) =
    (monoidBarMap (I.reverseOppositeHatGLIso n).hom ≫
      (monoidBarReverseOppositeIso (I.hatGL n)).hom) ≫ _
  rw [← Category.assoc, ← monoidBarMap_comp, I.reverseOppositeAffineIso_section,
    monoidBarMap_comp, Category.assoc, monoidBarReverseOppositeIso_natural, ← Category.assoc]

/-- 概要：反対転置の実 H_* 同型は標準包含と可換。
方針：実 bar 正方形と実鎖反転から得た自然同型の自然性を合成する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実相対加群同型の正方形。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso_section
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    F.map (monoidBarMap (simplicialActionProductSection
        (I.reverseOpposite.hatGLColumnAction n))) ≫
        (I.reverseOppositeAffineHomologyIso n F hF).hom =
      (I.reverseOppositeHatGLHomologyIso n F hF).hom ≫
        F.map (monoidBarMap (I.rowAffineSection n)) := by
  change F.map _ ≫ (F.map (I.reverseOppositeAffineBarIso n).hom ≫
      hF.reversalNatIso.hom.app (monoidBar (I.rowAffine n))) =
    (F.map (I.reverseOppositeHatGLBarIso n).hom ≫
      hF.reversalNatIso.hom.app (monoidBar (I.hatGL n))) ≫ _
  rw [← Category.assoc, ← F.map_comp, I.reverseOppositeAffineBarIso_section,
    F.map_comp, Category.assoc]
  have hn := hF.reversalNatIso.hom.naturality (monoidBarMap (I.rowAffineSection n))
  change F.map (SSet.opFunctor.map (monoidBarMap (I.rowAffineSection n))) ≫ _ = _ at hn
  rw [hn, ← Category.assoc]

/-- 概要：行側半直積の実相対 bar 加群。
方針：実標準包含の H_* の像による通常商を取る。
規約：SW92 §1.2、非被約 H_* を保つ。使われ方：実行側の零化の値域。 -/
def NonUnitalSimplicialRing.relativeRowAffineModule
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    ModuleCat.{u} ℤ := relativeModule (F.map (monoidBarMap (I.rowAffineSection n)))

/-- 概要：反対係数の列側と元の行側の実相対 bar 同型。
方針：基底と全空間の実 H_* 同型を、可換な標準包含の像の商へ降ろす。
規約：KST Proposition 4.14、SW92 §1.2。相対同型を新しい仮定にしない。
使われ方：列側の実低次零化を行側へ移す。 -/
def NonUnitalSimplicialRing.reverseOppositeRelativeAffineIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    relativeBarModule F (I.reverseOpposite.hatGLColumnAction n) ≅
      I.relativeRowAffineModule n F :=
  relativeModuleIso _ _ (I.reverseOppositeHatGLHomologyIso n F hF)
    (I.reverseOppositeAffineHomologyIso n F hF)
    (I.reverseOppositeAffineHomologyIso_section n F hF)

end SerrePositivity.KST.ProExcision
