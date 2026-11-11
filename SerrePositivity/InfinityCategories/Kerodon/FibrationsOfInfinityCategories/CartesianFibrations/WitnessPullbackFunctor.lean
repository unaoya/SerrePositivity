module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPre
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PullbackArrowFunctor

/-!
概要：実際の表現空間を固定した底上の圏の反変関手に束ねる。
方針：底変換の射の図式の pullback 正方形で表現を前合成する。
規約：全高次の図式と全空間の写像を厳密に保持する。
使われ方：pushout・非交和・骨格列に沿う表現の降下。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底上の対象ごとの実際の表現空間の反変関手。
方針：底変換の各 pullback 正方形を表現空間の前合成へ移す。
規約：引き戻しは可変の底を第一因子に取る。
使われ方：底の貼り合わせを表現空間の極限へ移す。 -/
def transportWitnessPullbackFunctor {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : (Over B)ᵒᵖ ⥤ SSet.{u + 1} where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).obj a.unop).hom
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map f.unop)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor_isPullback p f.unop)
  map_id a := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).obj a.unop).hom)).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι, unop_id, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map_id,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_id, Category.comp_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).obj Z.unop).hom)).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι]
    change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map (g.unop ≫ f.unop)) = _
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_comp, Category.assoc]

/-- 概要：底上の表現空間から周囲の四角形空間への包含は自然。
方針：pullback 正方形の前合成の包含公式を使う。
規約：全高次単体の自然変換。
使われ方：表現の降下を周囲の四角形の降下へ移す。 -/
def transportWitnessPullbackInclusion {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    transportWitnessPullbackFunctor p ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor where
  app a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).obj a.unop).hom
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).map f.unop)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor_isPullback p f.unop)

/-- 概要：底上の余錐の各項へ実際の表現を制限する錐。
方針：表現空間の反変関手で反対の錐を写す。
規約：余極限性は錐の定義に不要。
使われ方：表現空間の降下の候補となる極限錐。 -/
def transportWitnessColimitCone {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {J : Type v} [Category.{w} J] {D : J ⥤ Over B} (c : Cocone D) :
    Cone (D.op ⋙ transportWitnessPullbackFunctor p) :=
  (transportWitnessPullbackFunctor p).mapCone c.op

/-- 概要：表現空間の錐から周囲の四角形の錐を回収する。
方針：自然な包含で全ての脚を後合成する。
規約：パラメーターを保つ。
使われ方：周囲の四角形を貼ってから表現条件を反映する。 -/
def transportWitnessConeToSquare {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {J : Type v} [Category.{w} J] {D : J ⥤ Over B}
    (s : Cone (D.op ⋙ transportWitnessPullbackFunctor p)) :
    Cone ((D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullbackArrowFunctor p).op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFunctor) :=
  (Cone.postcompose (Functor.whiskerLeft D.op (transportWitnessPullbackInclusion p))).obj s

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
