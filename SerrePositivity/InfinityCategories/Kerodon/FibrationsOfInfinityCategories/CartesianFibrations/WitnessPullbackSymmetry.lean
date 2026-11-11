module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPullbackFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessTotalIso

/-!
概要：底を第一因子に取る降下の表現空間を従来の第二射影のモデルと結ぶ。
方針：pullback の対称同型を全空間の同型による表現空間の同型へ移す。
規約：底側の分類図式を厳密に保つ。
使われ方：降下定理に既存の制限写像の充填性を接続する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

local instance arrowMkLeftFibration {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (Arrow.mk p).hom := by simpa only [Arrow.mk_hom]

local instance pullbackSndLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

local instance pullbackFstLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst g p) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst g p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：底を第一因子に取る表現空間と第二因子に取る表現空間は厳密に同型。
方針：pullback の対称同型で全空間の表現を前合成する。
規約：同型の向きは従来の制限の値から降下関手の値へ。
使われ方：充填定理を降下の標準モデルへ移す。 -/
def transportWitnessPullbackSymmetry {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g) ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessTotalIso (pullback.fst g p) (pullback.snd p g)
    (pullbackSymmetry g p) (pullbackSymmetry_hom_comp_snd g p)

/-- 概要：pullback の対称比較は周囲の四角形の全空間の前合成を回収する。
方針：全空間の同型の包含公式。
規約：全次数の厳密な可換性。
使われ方：制限写像との比較。 -/
lemma transportWitnessPullbackSymmetry_hom_ι {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    (transportWitnessPullbackSymmetry p g).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (pullback.fst g p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (pullback.snd p g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre (pullback.fst g p) (pullback.snd p g)
          (pullbackSymmetry g p).hom (pullbackSymmetry_hom_comp_snd g p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessTotalIso_hom_ι _ _ _ _

/-- 概要：底の射を第一因子に置く標準 pullback 正方形。
方針：二つの射影を射の圏の射へ束ねる。
規約：底側は g、全空間側は第二射影。
使われ方：降下で用いる実際の底変換の制限。 -/
def transportPullbackSquare {E B D : SSet.{u + 1}} (p : E ⟶ B) (g : D ⟶ B) :
    Arrow.mk (pullback.fst g p) ⟶ Arrow.mk p :=
  Arrow.homMk (pullback.snd g p) g pullback.condition.symm

/-- 概要：標準底変換正方形は pullback。
方針：標準 pullback 四角形の対称性。
規約：left fibration 性は不要。
使われ方：表現の前合成の定義。 -/
lemma transportPullbackSquare_isPullback {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) :
    IsPullback (transportPullbackSquare p g).left (pullback.fst g p)
      p (transportPullbackSquare p g).right :=
  (IsPullback.of_hasPullback g p).flip

/-- 概要：四角形の従来の制限と対称比較の合成は標準正方形の前合成。
方針：二射影で内部 Hom の合成と対称同型の射影公式を使う。
規約：底側と全空間側をともに厳密に保つ。
使われ方：表現空間の制限の比較の周囲の等式。 -/
lemma transportSquareRestriction_pullbackSymmetry {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre (pullback.fst g p) (pullback.snd p g)
        (pullbackSymmetry g p).hom (pullbackSymmetry_hom_comp_snd g p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre (transportPullbackSquare p g) := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.fst g p) =
      _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.fst g p)
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre (transportPullbackSquare p g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.fst g p) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p ≫ (pre (pullback.snd g p)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity := by
      simpa only [transportPullbackSquare, Arrow.mk_hom, Arrow.homMk_left] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_pointed (transportPullbackSquare p g)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre_pointed, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_pointed, Category.assoc, h]
    change _ ≫ (pre (pullback.fst p g)).app _ ≫
      (pre (pullbackSymmetry g p).hom).app _ = _ ≫ (pre (pullback.snd g p)).app _
    rw [← NatTrans.comp_app, ← pre_map, pullbackSymmetry_hom_comp_fst]
  · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.fst g p) =
      _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.fst g p)
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre (transportPullbackSquare p g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.fst g p) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p ≫ (pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := by
      simpa only [transportPullbackSquare, Arrow.mk_hom, Arrow.homMk_right] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_diagram (transportPullbackSquare p g)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre_diagram,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_diagram, h]

/-- 概要：従来の制限は対称同型の後で標準 pullback 正方形の前合成と一致する。
方針：全部分複体の包含後に四角形の比較を使う。
規約：全高次単体の厳密な等式。
使われ方：制限の Kan fibration 性を降下のモデルへ移す。 -/
lemma transportWitnessRestriction_pullbackSymmetry {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g ≫ (transportWitnessPullbackSymmetry p g).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre (transportPullbackSquare p g)
        (transportPullbackSquare_isPullback p g) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (pullback.fst g p))).1
  rw [Category.assoc, transportWitnessPullbackSymmetry_hom_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_ι, Category.assoc,
    transportSquareRestriction_pullbackSymmetry]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι (transportPullbackSquare p g)
    (transportPullbackSquare_isPullback p g)).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
