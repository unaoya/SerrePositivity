module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityNativeComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxInputComparison
public import SerrePositivity.KST.SConstruction.PerfectIdentityLaxSequence
/-!
概要：未供給の恒等二脚・元二脚の lax 全比較について、必要な対象と二辺を固定する。
方針：固定 ν の実対角・実 cone 差と、元二脚の左右射影の全関手同型を保持する。
規約：この入力型は存在証明ではない。上下二胞体を含む LT 全長方形比較は別工程。
使われ方：ユーザー経由の D2 供給依頼の正確な型と、後続の特殊化の接続口。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Cν" => dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)
local notation "Lν" => dgKInputStableValue R (dgOdotMilnorIdentityGluingInput R d)
local notation "Dν" => dgKInputStableValue R (dgOdotMilnorIdentityDifferenceInput R d)
/-- 概要：恒等 Hom gluing と恒等 lax 圏の未供給全比較。
方針：対角と同じ実 cone 差を同時に保持する。規約：存在は仮定しない。
使われ方：実右面の指定境界を構成するための D2 供給型。 -/
structure DGOdotMilnorIdentityLaxComparisonInput where
  gluing : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (Lν).obj (laxCategory (𝟙 (Cν)) (𝟙 (Cν))).obj
  difference : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (Dν).obj (Cν).obj
  diagonal : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)).hom ≫ gluing.hom)
    (IdentityLax.exactDiagonal (Cν)).hom
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (gluing.hom ≫ (exactLaxDifference (𝟙 (Cν)) (𝟙 (Cν))).hom)
    ((dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)).hom ≫ difference.hom)

/-- 概要：導来係数基底の lax 模型と元の二脚の lax 模型の未供給比較。
方針：既存の左右入力同値を使う射影の全関手同型を指定する。
規約：上下二胞体や零化面の全比較の完成を主張しない。
使われ方：元二脚の LT 結論へ接続する D2 供給型。 -/
structure DGOdotMilnorOriginalLaxComparisonInput where
  gluing : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgOdotMilnorLaxCategory R d).obj (dgOdotPerfLaxCategory R d).obj
  fst : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (gluing.hom ≫ (laxFst (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((laxFst (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
      (dgOdotMilnorLaxLeftInputEquivalence R d).inv)
  snd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (gluing.hom ≫ (laxSnd (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((laxSnd (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
      (dgOdotMilnorLaxRightInputEquivalence R d).inv)
end SerrePositivity.KST.SConstruction
