module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex

/-!
概要：始点を保つ切断制限は全 left fibrations 上の大域的な関手同型。
方針：二つの始点制限の同値性で前合成の比較を消去する。
規約：制限射は単射でなくてよい。
使われ方：単体圏上の coherent な切断の図式を元の底へ降ろす条件。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：left anodyne な底上の射への切断制限は trivial Kan fibration。
方針：底の可換性を消去し既存の相対前合成の結果に戻す。
規約：底の充填性は不要。
使われ方：始点を保つ一般の制限の同値性を検出する。 -/
lemma relativeFunctorOverPre_trivialKanFibration_of_leftAnodyne {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : Over B} (f : a ⟶ b)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions f.left) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) := by
  obtain ⟨A, a, rfl⟩ := Over.mk_surjective a
  obtain ⟨B', b, rfl⟩ := Over.mk_surjective b
  obtain ⟨f, h, rfl⟩ := Over.homMk_surjective f
  change A ⟶ B' at f
  change f ≫ b = a at h
  subst a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_trivialKanFibration p b f hf

/-- 概要：同じ始点からの二つの left anodyne な比較を保つ切断制限は同値。
方針：始点制限との合成をもう一つの始点制限へ戻し二辺の同値を消去する。
規約：比較射 f 自体の単射性は仮定しない。
使われ方：退化も含む始点を保つ単体作用素の制限。 -/
lemma relativeFunctorOverPre_isQCatEquivalence_of_initialComparison {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b c : Over B}
    (f : a ⟶ b) (r : c ⟶ a) (s : c ⟶ b)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions r.left) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions s.left)
    (h : r ≫ f = s) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) := by
  have := relativeFunctorOverPre_trivialKanFibration_of_leftAnodyne p r hr
  have := relativeFunctorOverPre_trivialKanFibration_of_leftAnodyne p s hs
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p r)).cancel_right
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp, h]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 概要：始点を保つ一般の切断制限は全対象上で一つの関手同型。
方針：各対象の制限の同値性を豊穣比較の同型判定へ渡す。
規約：逆射を対象ごとに独立には選ばない。
使われ方：coherent な共同切断評価で可逆にすべき射の検証。 -/
def relativeSectionInitialRestrictionIso {B : SSet.{u}} {a b c : Over B}
    (f : a ⟶ b) (r : c ⟶ a) (s : c ⟶ b)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions r.left) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions s.left)
    (h : r ≫ f = s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison f)
  intro p
  exact relativeFunctorOverPre_isQCatEquivalence_of_initialComparison p.val.hom f r s hr hs h

/-- 概要：標準単体の始点を保つ射の切断制限は各 left fibration で同値。
方針：共通の始点の二つの包含で制限し同値性を反映する。
規約：射自体の単射性は不要。
使われ方：共同切断の図式で始点を保つ射の可逆性を示す。 -/
lemma relativeFunctorOverPre_isQCatEquivalence_of_firstVertex {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {m n : ℕ}
    {a : (Δ[m] : SSet.{u}) ⟶ B} {b : (Δ[n] : SSet.{u}) ⟶ B}
    (f : Over.mk a ⟶ Over.mk b)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m ≫ f.left = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) := by
  let c := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ≫ b)
  let r : c ⟶ Over.mk a := Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m) (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m ≫ a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ≫ b
    have hw : f.left ≫ b = a := f.w
    rw [← hw, ← Category.assoc, hf])
  let s : c ⟶ Over.mk b := Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n) rfl
  apply relativeFunctorOverPre_isQCatEquivalence_of_initialComparison p f r s
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne m) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne n)
  apply Over.OverMorphism.ext
  exact hf

/-- 概要：標準単体の始点を保つ底上の射の切断制限は全対象上で関手同型。
方針：各対象の同値性を豊穣比較の同型判定へ渡す。
規約：非単射な作用素を含む。
使われ方：底の単体圏の始点を保つ射を共同評価で反転する。 -/
def relativeSectionFirstVertexRestrictionIso {B : SSet.{u}} {m n : ℕ}
    {a : (Δ[m] : SSet.{u}) ⟶ B} {b : (Δ[n] : SSet.{u}) ⟶ B}
    (f : Over.mk a ⟶ Over.mk b)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m ≫ f.left = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk a))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison f)
  intro p
  exact relativeFunctorOverPre_isQCatEquivalence_of_firstVertex p.val.hom f hf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
