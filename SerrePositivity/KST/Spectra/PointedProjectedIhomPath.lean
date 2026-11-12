module

public import SerrePositivity.KST.Spectra.PointedIhomIntervalNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalInputBoundary

/-!
概要：入力制限と射影を持つ同じ区間を、全パラメータ内部 Hom へ移す座標。
方針：内部 Hom の前後合成の厳密自然性で、同じ合成入力へまとめる。
規約：充填や区間選択不要。使われ方：実際の随伴比較辺の全族終辺照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 入力制限・射影・全族作用は、同じ区間への合成入力の制限として表示できる。 -/
lemma projectedIhomPre_path {D E A B : PointedSimplicialSet.{u}} {f g : D ⟶ D}
    (R : VerticalPath (PointedObject.toPoint D) f g) (i : A ⟶ D) (q : D ⟶ E)
    (P : PointedSimplicialSet.{u}) (j : B ⟶ PointedObject.basedHom P A) :
    (((((R.pre i).basedPost q).basedIhomMap P).pre j).path) =
      ((((R.basedIhomMap P).basedPost (PointedObject.basedHomMap P q)).pre
        (j ≫ PointedObject.basedHomMap P i)).path) := by
  change (((R.pre i).basedPost q).basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P E)).right =
    ((R.basedIhomMap P).basedPost (PointedObject.basedHomMap P q)).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ PointedObject.basedHomMap P i) (PointedObject.basedHom P E)).right
  rw [basedIhomMap_post_path]
  change (((R.pre i).basedIhomMap P).path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom P A)
        (PointedObject.basedHomMap P q)).right) ≫ _ = _
  rw [basedIhomMap_pre_path_natural]
  have he := (R.basedIhomMap P).pre_basedPost_path
    (PointedObject.basedHomMap P i) (PointedObject.basedHomMap P q)
  exact (congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j _).right) he.symm).trans
    (((R.basedIhomMap P).basedPost (PointedObject.basedHomMap P q)).pre_pre_path
      (PointedObject.basedHomMap P i) j)

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
