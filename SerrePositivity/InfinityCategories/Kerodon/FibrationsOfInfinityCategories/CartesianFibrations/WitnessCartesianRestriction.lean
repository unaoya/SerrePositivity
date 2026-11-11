module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPre
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessTotalIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessInnerAnodyne

/-!
概要：任意の pullback 正方形の前合成を実際の底変換の制限と同型で結ぶ。
方針：全空間を標準 pullback に同定し、四角形の二射影で比較する。
規約：標準 pullback の表示を指定する仮定は不要。
使われ方：降下関手の実際の射に制限の充填性を移す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

local instance cartesianRestrictionPullbackLF {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：pullback 正方形の全空間同型と実際の四角形の制限は前合成を回収する。
方針：二射影と標準 pullback への同型の射影公式を使う。
規約：充填性は不要。
使われ方：表現空間の制限と一般の pullback 前合成の比較。 -/
lemma transportSquarePre_eq_restriction_totalPre {p q : Arrow SSet.{u + 1}}
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction q.hom f.right ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre p.hom (pullback.snd q.hom f.right)
        hf.isoPullback.hom hf.isoPullback_hom_snd := by
  apply pullback.hom_ext
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom =
      (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p.hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_pointed, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre_pointed,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_pointed, Category.assoc,
      ← NatTrans.comp_app, ← pre_map, hf.isoPullback_hom_fst]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom =
      (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p.hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_diagram, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTotalPre_diagram,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_diagram]

/-- 概要：pullback 正方形の表現の前合成は実際の制限と全空間同型の合成。
方針：表現空間の包含後に四角形の比較を使う。
規約：全高次単体で底側と全空間側を保つ。
使われ方：Kan fibration と全境界充填を任意の pullback 表示へ移す。 -/
lemma transportWitnessPre_eq_restriction_totalIso {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction q.hom f.right ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessTotalIso p.hom (pullback.snd q.hom f.right)
        hf.isoPullback hf.isoPullback_hom_snd).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p.hom)).1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessTotalIso_hom_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_ι, Category.assoc,
    transportSquarePre_eq_restriction_totalPre f hf]

/-- 概要：底側が単射の pullback 正方形の表現の前合成は Kan fibration。
方針：実際の制限の Kan fibration と全空間同型を合成する。
規約：全空間を特定の pullback モデルに固定しない。
使われ方：降下関手の単射に沿う遷移写像。 -/
lemma transportWitnessPre_fibration {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf) := by
  rw [transportWitnessPre_eq_restriction_totalIso f hf]
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionFibration.transportWitnessRestriction_fibration q.hom f.right
  infer_instance

/-- 概要：底側が inner anodyne の pullback 前合成は trivial Kan fibration。
方針：実際の制限の全境界充填と全空間同型を合成する。
規約：非空性を仮定しない。
使われ方：内ホーンによる表現の復元の表示独立性。 -/
lemma transportWitnessPre_trivialKanFibration {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (h : innerAnodyneExtensions f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf) := by
  rw [transportWitnessPre_eq_restriction_totalIso f hf]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_trivialKanFibration_of_innerAnodyne q.hom f.right h).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
