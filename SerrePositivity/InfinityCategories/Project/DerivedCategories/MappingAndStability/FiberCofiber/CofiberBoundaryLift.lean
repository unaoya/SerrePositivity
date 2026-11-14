module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberBoundaryTriangleCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.PushoutBoundaryEquations

/-! # 実際の cofiber 境界の二未知 cochain

概要：coslice 境界の残差から Q・A の未知成分を構成し、その微分方程式を証明する。
方針：q = −n−1 の符号を照合し、実境界の Bianchi 条件を逆 Hom 座標の明示解へ渡す。
規約：単体の全方程式は後続工程で検証する。使われ方：D7 の coslice 充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 概要：境界の次数と Bianchi の符号は一致する。
方針：q = −(n+1) と整数符号の反転不変性を使う。
規約：n = 0 も含む。使われ方：実境界の残差条件の代入。 -/
lemma cofiberBoundaryDegree_negOnePow (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow = ((n : ℤ) + 1).negOnePow := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n = -((n : ℤ) + 1) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]
    omega
  rw [h, Int.negOnePow_neg]

/-- 概要：Q 側の未知成分を三成分逆座標から構成する。
方針：三角形残差の差と二脚の残差を逆座標へ入れる。
規約：次数は q+1。使われ方：後続成分の補正。 -/
def cofiberBoundaryLiftQ {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    Cochain (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber f g) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget f g b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)

/-- 概要：A 側の未知成分を右三角形残差の符号倍に取る。
方針：右三角形の標準ホモトピーが零であることに合わせる。
規約：次数は q。使われ方：共通 A 面の補正。 -/
def cofiberBoundaryLiftA {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    Cochain A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget f g b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb

/-- 概要：実境界から構成した Q 成分の微分は後続残差に等しい。
方針：四つの既証明の整合条件を明示解の微分定理へ代入する。
規約：残差の整合条件を追加仮定しない。使われ方：後続未知集合の方程式。 -/
lemma cofiberBoundaryLiftQ_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1 + 1)
      (cofiberBoundaryLiftQ f g b hb) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_differential_of_residuals f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)
  · simpa only [cofiberBoundaryDegree_negOnePow] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB_differential f g b hb
  · simpa only [cofiberBoundaryDegree_negOnePow] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC_differential f g b hb
  · simpa only [cofiberBoundaryDegree_negOnePow] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB_differential f g b hb
  · simpa only [cofiberBoundaryDegree_negOnePow] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC_differential f g b hb

/-- 概要：実境界から構成した A 成分は対角を含む微分方程式を満たす。
方針：右三角形の整合条件を A 側明示解の定理へ渡す。
規約：Q 成分は上で構成したものを使う。使われ方：A 側未知集合の方程式。 -/
lemma cofiberBoundaryLiftA_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)
      (cofiberBoundaryLiftA f g b hb) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb -
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow •
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal f g)).comp (cofiberBoundaryLiftQ f g b hb)
          (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutBoundary_A_equation f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)
  simpa only [cofiberBoundaryDegree_negOnePow] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC_differential f g b hb

/-- 概要：Q 成分の inclusionB 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_inclusionB {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g)).comp (cofiberBoundaryLiftQ f g b hb)
      (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow • (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_inclusionB f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)

/-- 概要：Q 成分の inclusionC 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_inclusionC {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)).comp (cofiberBoundaryLiftQ f g b hb)
      (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow • (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_inclusionC f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)

/-- 概要：Q 成分の homotopy 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_homotopy {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g)).comp (cofiberBoundaryLiftQ f g b hb) (by omega) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow •
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_homotopy f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)

/-- 概要：Q 成分の diagonal 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_diagonal {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal f g)).comp (cofiberBoundaryLiftQ f g b hb)
      (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow • ((Cochain.ofHom g).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
        (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_diagonal f g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsB f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsC f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAB f g b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsAC f g b hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
