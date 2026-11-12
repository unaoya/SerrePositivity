module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonal
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：共通の単体集合へ写る二つの単体集合の relative join。
方針：join の誘導射を区間付き対角へ引き戻し、両端の包含を引き戻しへ持ち上げる。
規約：fibration 性や quasicategory 性は構成の仮定に含めない。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、1 単体上の transport と scaffold の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：共通の底へ写る二つの単体集合の relative join。
方針：joinMap f g を底の区間付き対角へ引き戻す。
規約：区間成分を第一因子とする。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、通常の関手を transport として表す全空間。 -/
@[kerodon 0242]
noncomputable def relativeJoin {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)

/-- 概要：relative join の標準 1 単体への射影。
方針：引き戻しの第二射影に区間成分の第一射影を合成する。
規約：零端が X、一端が Y に対応する。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、区間上の fibration の候補の射影。 -/
@[kerodon 0242]
noncomputable def relativeJoinProjection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoin f g ⟶ (Δ[1] : SSet.{u}) :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) ≫ fst (Δ[1] : SSet.{u}) S

/-- 概要：relative join の左因子の包含。
方針：通常の join の左包含と底の区間の零端を引き戻しへ持ち上げる。
規約：底の係数は f で写す。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、零端の fiber と元の X の比較。 -/
noncomputable def relativeJoinInl {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    X ⟶ relativeJoin f g :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 S) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_zero_joinDiagonal])

/-- 概要：relative join の右因子の包含。
方針：通常の join の右包含と底の区間の一端を引き戻しへ持ち上げる。
規約：底の係数は g で写す。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、一端の fiber と元の Y の比較。 -/
noncomputable def relativeJoinInr {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Y ⟶ relativeJoin f g :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y) (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_one_joinDiagonal])

/-- 概要：relative join の左包含を通常の join へ写すと標準の左包含となる。
方針：引き戻しの持ち上げの第一射影の計算則を使う。
規約：相対的な係数の条件を忘れた比較。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の左端の計算。 -/
lemma relativeJoinInl_fst {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInl f g ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl X Y :=
  pullback.lift_fst _ _ _

/-- 概要：relative join の右包含を通常の join へ写すと標準の右包含となる。
方針：引き戻しの持ち上げの第一射影の計算則を使う。
規約：相対的な係数の条件を忘れた比較。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の右端の計算。 -/
lemma relativeJoinInr_fst {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInr f g ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr X Y :=
  pullback.lift_fst _ _ _

/-- 概要：relative join の左包含は区間の零端の上にある。
方針：引き戻しの第二射影と prism の第一射影を計算する。
規約：射影先の定値頂点は標準 1 単体の零頂点。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、零端の fiber の同定。 -/
lemma relativeJoinInl_projection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInl f g ≫ relativeJoinProjection f g =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [relativeJoinProjection, ← Category.assoc]
  change (relativeJoinInl f g ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) ≫ _ = _
  rw [show relativeJoinInl f g ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) =
    f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 S from pullback.lift_snd _ _ _]
  rw [Category.assoc]
  change f ≫ SSet.const _ = _
  exact SSet.comp_const _ _

/-- 概要：relative join の右包含は区間の一端の上にある。
方針：引き戻しの第二射影と prism の第一射影を計算する。
規約：射影先の定値頂点は標準 1 単体の一頂点。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、一端の fiber の同定。 -/
lemma relativeJoinInr_projection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInr f g ≫ relativeJoinProjection f g =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [relativeJoinProjection, ← Category.assoc]
  change (relativeJoinInr f g ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) ≫ _ = _
  rw [show relativeJoinInr f g ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) =
    g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S from pullback.lift_snd _ _ _]
  rw [Category.assoc]
  change g ≫ SSet.const _ = _
  exact SSet.comp_const _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
