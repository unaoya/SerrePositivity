module

public import SerrePositivity.KST.Spectra.FreePointedHomRestriction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget

/-!
概要：自由なパラメータからの cotensor を、点つき Hom に値を取る通常の関数複体へ表示する。
方針：点つき内部 Hom の交換と自由基点の制限同型を合成する。
規約：全単体次数の自然同型。使われ方：実区間・正方形の自由区間座標への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedCotensorCoordinates

/-- 自由パラメータの cotensor を値とする Hom の、元の関数複体の座標。 -/
def iso (K : SSet.{u}) (T E : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom T
      (PointedObject.basedHom (PointedObject.adjoin K) E)).right ≅
    (ihom K).obj (PointedObject.basedHom T E).right :=
  PointedSimplicialSet.forget.mapIso (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso T (PointedObject.adjoin K) E) ≪≫
    FreePointedHomRestriction.iso K (PointedObject.basedHom T E)

/-- 座標表示は点つき源の制限について自然。 -/
lemma natural_source (K : SSet.{u}) {T U : PointedSimplicialSet.{u}}
    (i : T ⟶ U) (E : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i
      (PointedObject.basedHom (PointedObject.adjoin K) E)).right ≫ (iso K T E).hom =
    (iso K U E).hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E).right := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left i (PointedObject.adjoin K) E
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  have hh := congrArg Under.Hom.right h
  simp only [Under.comp_right] at hh
  simp only [iso, Iso.trans_hom, Functor.mapIso_hom, FreePointedHomRestriction.iso]
  rw [← Category.assoc]
  erw [hh]
  rw [Category.assoc]
  erw [FreePointedHomRestriction.natural_post K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E)]
  exact (Category.assoc _ _ _).symm

/-- 座標表示は標的への後合成について自然。 -/
lemma natural_target (K : SSet.{u}) (T : PointedSimplicialSet.{u})
    {E V : PointedSimplicialSet.{u}} (f : E ⟶ V) :
    (PointedObject.basedHomMap T (PointedObject.basedHomMap (PointedObject.adjoin K) f)).right ≫
      (iso K T V).hom =
    (iso K T E).hom ≫ (ihom K).map (PointedObject.basedHomMap T f).right := by
  have hh := congrArg Under.Hom.right
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post T (PointedObject.adjoin K) f)
  simp only [Under.comp_right] at hh
  simp only [iso, Iso.trans_hom, Functor.mapIso_hom, FreePointedHomRestriction.iso]
  rw [← Category.assoc]
  erw [hh]
  rw [Category.assoc]
  erw [FreePointedHomRestriction.natural_post K (PointedObject.basedHomMap T f)]
  exact (Category.assoc _ _ _).symm

/-- 座標表示は自由パラメータの任意の制限について自然。 -/
lemma natural_parameter {K L : SSet.{u}} (j : L ⟶ K)
    (T E : PointedSimplicialSet.{u}) :
    (PointedObject.basedHomMap T
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) E)).right ≫
        (iso L T E).hom =
    (iso K T E).hom ≫ (MonoidalClosed.pre j).app (PointedObject.basedHom T E).right := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right T (PointedObject.adjoinFunctor.map j) E
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  have hh := congrArg Under.Hom.right h
  simp only [Under.comp_right] at hh
  simp only [iso, Iso.trans_hom, Functor.mapIso_hom, FreePointedHomRestriction.iso]
  rw [← Category.assoc]
  erw [hh]
  rw [Category.assoc]
  erw [FreePointedHomRestriction.natural_pre j (PointedObject.basedHom T E)]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.Spectra.PointedCotensorCoordinates
