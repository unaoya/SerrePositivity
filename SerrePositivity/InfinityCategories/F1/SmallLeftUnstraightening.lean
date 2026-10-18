module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSmallness
public import SerrePositivity.InfinityCategories.F1.SmallFibration
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInfinity

/-!
概要：一般の coherent な空間値図式の小さい unstraightening。
方針：引き戻しの各次数の小ささで全空間を縮小し、射影と left fibration 性を移す。
規約：F は小さい底の宇宙持ち上げから宇宙 u の空間の coherent nerve への任意の写像。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式を strict transport と比較するための対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい底を持ち上げた図式の unstraightening の各次数は元の宇宙に小さい。
方針：底の ULift の小ささを明示して一般の引き戻しの判定を適用する。
規約：追加の宇宙は u+1。
使われ方：Kerodon Corollary 5.6.0.6、小さい全空間の縮小に必要な小ささの束縛。 -/
instance leftUnstraightening_uliftBase_obj_small {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((leftUnstraightening F).obj n) := by
  have (k : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj B).obj k) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (B.obj k)))
  exact leftUnstraightening_obj_small F n

/-- 概要：一般の coherent な図式の unstraightening の小さい全空間。
方針：普遍的な coslice の引き戻しを次数ごとに縮小する。
規約：底 B の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、left fibrations の小さい ∞ 圏の対象の構成。 -/
noncomputable def smallLeftUnstraightening {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : SSet.{u} :=
  smallSimplicialSet.{u, u + 1} (leftUnstraightening F)

/-- 概要：小さい unstraightening の持ち上げは元の全空間と同型。
方針：次数ごとの縮小の同型を適用する。
規約：比較は全空間の厳密な同型。
使われ方：Kerodon Corollary 5.6.0.6、元の普遍的な引き戻しとの比較。 -/
noncomputable def smallLeftUnstraighteningIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F) ≅ leftUnstraightening F :=
  smallSimplicialSetIso.{u, u + 1} (leftUnstraightening F)

/-- 概要：小さい unstraightening から元の小さい底への射影。
方針：縮小した全空間からの射影を元の宇宙へ戻す。
規約：射影の標的は持ち上げる前の B。
使われ方：Kerodon Corollary 5.6.0.6、小さい left fibration としての unstraightening。 -/
noncomputable def smallLeftUnstraighteningProjection {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    smallLeftUnstraightening F ⟶ B :=
  smallSimplicialProjection (leftUnstraighteningProjection F)

/-- 概要：小さい unstraightening の全空間の同型は底の射影と可換。
方針：縮小した射影の宇宙持ち上げの計算則を使う。
規約：底は持ち上げた B に揃える。
使われ方：Kerodon Corollary 5.6.0.6、小さい代表の fiber と元の fiber の比較。 -/
lemma smallLeftUnstraighteningIso_projection {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (smallLeftUnstraighteningIso F).hom ≫ leftUnstraighteningProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F) :=
  (smallSimplicialProjection_ulift (leftUnstraighteningProjection F)).symm

/-- 概要：小さい unstraightening の射影は left fibration。
方針：元の引き戻しの left fibration 性を縮小した射影へ移す。
規約：一般の coherent な図式を扱い、strict な図式に制限しない。
使われ方：Kerodon Corollary 5.6.0.6、分類の構成方向の小さい left fibration の充填性。 -/
instance smallLeftUnstraighteningProjection_leftFibration {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    LeftFibration (smallLeftUnstraighteningProjection F) :=
  inferInstanceAs (LeftFibration (smallSimplicialProjection (leftUnstraighteningProjection F)))

/-- 概要：小さい unstraightening を left fibrations の単体的圏の対象に束縛する。
方針：元の底への小さい射影とその充填性をまとめる。
規約：図式の同値類ではなく、選択した小さい全空間を持つ対象。
使われ方：Kerodon Corollary 5.6.0.6、straightening との対象での比較の始点。 -/
noncomputable def smallLeftUnstraighteningObject {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : LeftFibrationObject B :=
  ⟨Over.mk (smallLeftUnstraighteningProjection F),
    smallLeftUnstraighteningProjection_leftFibration F⟩

end SerrePositivity.InfinityCategories
