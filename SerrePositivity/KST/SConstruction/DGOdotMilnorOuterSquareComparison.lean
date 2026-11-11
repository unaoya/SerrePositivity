module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterSquareFrame
public import SerrePositivity.KST.SConstruction.StableZeroSquareComparison
public import SerrePositivity.KST.SConstruction.SquareFrameHomotopyPostcomp

/-!
概要：元始域外面の Cat^perf 全四角形を、元 LT の絶対外周全体へ比較する。
方針：元四境界を零対角の一意性で接合し、同じ充満忠実な包含で戻す。
規約：元 cell 始域の増大屋根・resolved 商・元二胞体を保持。D2 の追加入力は不要。
使われ方：元外周の指定三境界付き全図式認証の比較成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元実外周の四境界全比較を同じ StableInfinity 内に保持する。
方針：元全比較を同じ完備包含で後合成する。
規約：元四側面・四頂点経路を保持。使われ方：元共有零対角の接合。 -/
def dgOdotMilnorOuterRawSquareFrameComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare ((dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) ≫
      perfectStableInfinityInclusion))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare ((dgOdotMilnorActualOuterDiagram R d h).square ≫ perfectStableInfinityInclusion)) :=
  squareFrameHomotopyPostcomp (dgOdotMilnorOuterSquareFrameComparison R d h) perfectStableInfinityInclusion

/-- 概要：元始域外面の StableInfinity 全比較は元 LT 絶対外周の同じ全二胞体を保持する。
方針：元零角を保つ同じ四境界から共有対角を整列して接合する。
規約：元始域を増大屋根で保持。使われ方：元 Cat^perf 外周比較の逆像。 -/
def dgOdotMilnorOuterRawSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R) ≫ perfectStableInfinityInclusion)
    ((dgOdotMilnorActualOuterDiagram R d h).square ≫ perfectStableInfinityInclusion) :=
  stableZeroSquareComparison (dgOdotMilnorOuterRawSquareFrameComparison R d h)
    (dgOdotMilnorSourceNullOuterSquare_perfect_zero R d)

/-- 概要：元実始域外面は同じ元 LT 絶対外周全体と Cat^perf 内で同型。
方針：同じ StableInfinity 全比較を充満忠実な完備包含で戻す。
規約：元始域屋根・実商辺・元上下二胞体を保持。使われ方：外周全図式認証。 -/
def dgOdotMilnorOuterPerfectSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (dgOdotMilnorActualOuterDiagram R d h).square :=
  perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso (dgOdotMilnorOuterRawSquareComparison R d h)
end SerrePositivity.KST.SConstruction
