module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeDerivedHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.UniverseHomotopy

/-!
# 実正規化 probe Hom 比較 span の左射

概要：同じ標的置換の実 Hom 射を既存 D(R) と同じ宇宙へ送り、弱同値性を保つ。
方針：元の実単体的ホモトピー逆と両ホモトピーをそのまま持ち上げる。
規約：同じ中間項と元の augmentation を使う。
使われ方：元の標準 frame から既存 D(R) への実 Hom span。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def normalizedProbeDerivedSpanLeft (X Y : Complex A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (complexSemifreeResolutionValue A Y).val) ⟶
    SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj Y) :=
  SSet.uliftFunctor.{u + 1, u}.map (normalizedProbeTargetReplacementMap A X Y)

lemma normalizedProbeDerivedSpanLeft_homotopyEquivalence (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (normalizedProbeDerivedSpanLeft A X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    (normalizedProbeTargetReplacementMap_homotopyEquivalence A X Y)

end SerrePositivity.EInfinity.ComplexLimits
