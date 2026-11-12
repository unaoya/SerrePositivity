module
public import SerrePositivity.KST.SConstruction.PointedExtensionSpace
public import SerrePositivity.KST.SConstruction.PointedLiftSpace

/-! # 厳密に等しい制限射・底の射による選択空間の比較
概要：制限の表示を変えた延長空間と持ち上げ空間を同型で比較する。
方針：元の射の等号による移送を使い、写像空間への射影を厳密に保持する。
規約：同型は選択する実際の点つき射を変えない。
使われ方：恒等入力射の混合選択を元の構造射の因子選択へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 同じ制限射の二つの表示による延長選択空間の同型。 -/
def pointedExtensionBaseIso {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B)
    {h h' : A ⟶ Z} (e : h = h') : pointedExtensionSpace i h ≅ pointedExtensionSpace i h' :=
  eqToIso (congrArg (pointedExtensionSpace i) e)

/-- 延長選択空間の比較は、実際の写像空間への射影を厳密に保つ。 -/
lemma pointedExtensionBaseIso_projection {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B)
    {h h' : A ⟶ Z} (e : h = h') :
    (pointedExtensionBaseIso i e).hom ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right (SSet.yonedaEquiv.symm (familyVertex h')) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right (SSet.yonedaEquiv.symm (familyVertex h)) := by
  cases e
  simp only [pointedExtensionBaseIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- 延長選択の比較後に回収する点つき射は元の射そのもの。 -/
lemma pointedExtensionBaseIso_map {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B)
    {h h' : A ⟶ Z} (e : h = h') (v : (pointedExtensionSpace i h) _⦋0⦌) :
    pointedExtensionMap i h' ((pointedExtensionBaseIso i e).hom.app (Opposite.op ⦋0⦌) v) =
      pointedExtensionMap i h v := by
  cases e
  rfl

/-- 同じ底の射の二つの表示による持ち上げ選択空間の同型。 -/
def pointedLiftBaseIso {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    {b b' : A ⟶ B} (e : b = b') : pointedLiftSpace p b ≅ pointedLiftSpace p b' :=
  eqToIso (congrArg (pointedLiftSpace p) e)

/-- 持ち上げ選択空間の比較は、実際の写像空間への射影を厳密に保つ。 -/
lemma pointedLiftBaseIso_projection {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    {b b' : A ⟶ B} (e : b = b') :
    (pointedLiftBaseIso p e).hom ≫
        pullback.fst (PointedObject.basedHomMap A p).right
          (SSet.yonedaEquiv.symm (familyVertex b')) =
      pullback.fst (PointedObject.basedHomMap A p).right
        (SSet.yonedaEquiv.symm (familyVertex b)) := by
  cases e
  simp only [pointedLiftBaseIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- 持ち上げ選択の比較後に回収する点つき射は元の射そのもの。 -/
lemma pointedLiftBaseIso_map {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    {b b' : A ⟶ B} (e : b = b') (v : (pointedLiftSpace p b) _⦋0⦌) :
    pointedLiftMap p b' ((pointedLiftBaseIso p e).hom.app (Opposite.op ⦋0⦌) v) =
      pointedLiftMap p b v := by
  cases e
  rfl

/-- 自然な評価射を合成した族も、底の射の表示の変更で厳密に保たれる。 -/
lemma pointedLiftBaseIso_evaluation {A E B R : PointedSimplicialSet.{u}} (p : E ⟶ B)
    {b b' : A ⟶ B} (e : b = b') (s : E ⟶ R) :
    (pointedLiftBaseIso p e).hom ≫
        (pullback.fst (PointedObject.basedHomMap A p).right
          (SSet.yonedaEquiv.symm (familyVertex b')) ≫ (PointedObject.basedHomMap A s).right) =
      pullback.fst (PointedObject.basedHomMap A p).right
        (SSet.yonedaEquiv.symm (familyVertex b)) ≫ (PointedObject.basedHomMap A s).right := by
  cases e
  simp only [pointedLiftBaseIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- 持ち上げを別の射で評価しても、底の表示の変更は回収する射を変えない。 -/
lemma pointedLiftBaseIso_map_post {A E B R : PointedSimplicialSet.{u}} (p : E ⟶ B)
    {b b' : A ⟶ B} (e : b = b') (s : E ⟶ R) (v : (pointedLiftSpace p b) _⦋0⦌) :
    pointedLiftMap p b' ((pointedLiftBaseIso p e).hom.app (Opposite.op ⦋0⦌) v) ≫ s =
      pointedLiftMap p b v ≫ s := by
  cases e
  rfl

end SerrePositivity.KST.SConstruction
