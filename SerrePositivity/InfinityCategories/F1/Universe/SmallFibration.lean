module

public import SerrePositivity.InfinityCategories.F1.Universe.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.F1.Universe.LeftFibrationReflection

/-!
概要：小さい底の宇宙持ち上げへの射を、小さい全空間上の射へ移す。
方針：縮小の同型で全空間を移し、射の ULift を外す。
規約：全空間の各次数の小ささを仮定し、left fibration 性も移す。
使われ方：Kerodon Corollary 5.6.0.6、coherent な unstraightening の小さい射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい底への大きい射影を縮小した全空間からの小さい射へ移す。
方針：全空間の同型の後に元の射を合成して、ULift を外す。
規約：小さい底 B は宇宙 u。
使われ方：Kerodon Corollary 5.6.0.6、小さい unstraightening の射影の構成。 -/
noncomputable def smallSimplicialProjection {X : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] {B : SSet.{u}}
    (p : X ⟶ (SSet.uliftFunctor.{v, u}).obj B) : smallSimplicialSet X ⟶ B :=
  uliftMorphismDown ((smallSimplicialSetIso X).hom ≫ p)

/-- 概要：縮小した射影を持ち上げると、元の射影を全空間の同型で引き戻した射になる。
方針：各次数で入力の縮小と出力の ULift の往復を計算する。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、縮小した射影と元の unstraightening の底上の比較。 -/
lemma smallSimplicialProjection_ulift {X : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] {B : SSet.{u}}
    (p : X ⟶ (SSet.uliftFunctor.{v, u}).obj B) :
    (SSet.uliftFunctor.{v, u}).map (smallSimplicialProjection p) =
      (smallSimplicialSetIso X).hom ≫ p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change ULift.up ((p.app n ((equivShrink (X.obj n)).symm x.down)).down) =
    p.app n ((equivShrink (X.obj n)).symm x.down)
  rfl

/-- 概要：全空間を縮小した射影は元の射影の left fibration 性を保つ。
方針：持ち上げた射影を同型と元の射の合成として判定し、宇宙持ち上げから反映する。
規約：底 B に quasicategory 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、小さい coherent unstraightening の充填性。 -/
instance smallSimplicialProjection_leftFibration {X : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] {B : SSet.{u}}
    (p : X ⟶ (SSet.uliftFunctor.{v, u}).obj B) [LeftFibration p] :
    LeftFibration (smallSimplicialProjection p) := by
  have : LeftFibration ((SSet.uliftFunctor.{v, u}).map (smallSimplicialProjection p)) := by
    rw [smallSimplicialProjection_ulift]
    exact ⟨leftFibrations.comp_mem _ _
      (leftFibrations.of_isIso (smallSimplicialSetIso X).hom) LeftFibration.mem⟩
  exact leftFibration_of_ulift (smallSimplicialProjection p)

end SerrePositivity.InfinityCategories
