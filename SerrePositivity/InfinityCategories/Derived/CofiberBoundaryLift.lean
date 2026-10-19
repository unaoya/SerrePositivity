module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryTriangleCompatibility
public import SerrePositivity.InfinityCategories.Derived.PushoutBoundaryEquations

/-! # 実際の cofiber 境界の二未知 cochain

概要：coslice 境界の残差から Q・A の未知成分を構成し、その微分方程式を証明する。
方針：q = −n−1 の符号を照合し、実境界の Bianchi 条件を逆 Hom 座標の明示解へ渡す。
規約：単体の全方程式は後続工程で検証する。使われ方：D7 の coslice 充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 概要：境界の次数と Bianchi の符号は一致する。
方針：q = −(n+1) と整数符号の反転不変性を使う。
規約：n = 0 も含む。使われ方：実境界の残差条件の代入。 -/
lemma cofiberBoundaryDegree_negOnePow (n : ℕ) :
    (cofiberBoundaryDegree n).negOnePow = ((n : ℤ) + 1).negOnePow := by
  have h : cofiberBoundaryDegree n = -((n : ℤ) + 1) := by
    dsimp only [cofiberBoundaryDegree]
    omega
  rw [h, Int.negOnePow_neg]

/-- 概要：Q 側の未知成分を三成分逆座標から構成する。
方針：三角形残差の差と二脚の残差を逆座標へ入れる。
規約：次数は q+1。使われ方：後続成分の補正。 -/
def cofiberBoundaryLiftQ {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (pushoutCofiber f g) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n + 1) :=
  pushoutHomBoundaryLift f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhsB f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb)

/-- 概要：A 側の未知成分を右三角形残差の符号倍に取る。
方針：右三角形の標準ホモトピーが零であることに合わせる。
規約：次数は q。使われ方：共通 A 面の補正。 -/
def cofiberBoundaryLiftA {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain A (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n) :=
  (cofiberBoundaryDegree n).negOnePow • cofiberBoundaryRhsAC f g b hb

/-- 概要：実境界から構成した Q 成分の微分は後続残差に等しい。
方針：四つの既証明の整合条件を明示解の微分定理へ代入する。
規約：残差の整合条件を追加仮定しない。使われ方：後続未知集合の方程式。 -/
lemma cofiberBoundaryLiftQ_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n + 1) (cofiberBoundaryDegree n + 1 + 1)
      (cofiberBoundaryLiftQ f g b hb) = cofiberBoundaryRhs0 f g b hb := by
  apply pushoutHomBoundaryLift_differential_of_residuals f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhs0 f g b hb) (cofiberBoundaryRhsB f g b hb)
    (cofiberBoundaryRhsC f g b hb) (cofiberBoundaryRhsA f g b hb)
    (cofiberBoundaryRhsAB f g b hb) (cofiberBoundaryRhsAC f g b hb)
  · simpa only [cofiberBoundaryDegree_negOnePow] using cofiberBoundaryRhsB_differential f g b hb
  · simpa only [cofiberBoundaryDegree_negOnePow] using cofiberBoundaryRhsC_differential f g b hb
  · simpa only [cofiberBoundaryDegree_negOnePow] using cofiberBoundaryRhsAB_differential f g b hb
  · simpa only [cofiberBoundaryDegree_negOnePow] using cofiberBoundaryRhsAC_differential f g b hb

/-- 概要：実境界から構成した A 成分は対角を含む微分方程式を満たす。
方針：右三角形の整合条件を A 側明示解の定理へ渡す。
規約：Q 成分は上で構成したものを使う。使われ方：A 側未知集合の方程式。 -/
lemma cofiberBoundaryLiftA_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n) (cofiberBoundaryDegree n + 1)
      (cofiberBoundaryLiftA f g b hb) = cofiberBoundaryRhsA f g b hb -
      (cofiberBoundaryDegree n).negOnePow •
        (Cochain.ofHom (pushoutDiagonal f g)).comp (cofiberBoundaryLiftQ f g b hb)
          (zero_add (cofiberBoundaryDegree n + 1)) := by
  apply pushoutBoundary_A_equation f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhsB f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsA f g b hb) (cofiberBoundaryRhsAB f g b hb)
    (cofiberBoundaryRhsAC f g b hb)
  simpa only [cofiberBoundaryDegree_negOnePow] using cofiberBoundaryRhsAC_differential f g b hb

/-- 概要：Q 成分の inclusionB 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_inclusionB {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (Cochain.ofHom (pushoutInclusionB f g)).comp (cofiberBoundaryLiftQ f g b hb)
      (zero_add (cofiberBoundaryDegree n + 1)) =
      (cofiberBoundaryDegree n).negOnePow • (cofiberBoundaryRhsB f g b hb) :=
  pushoutHomBoundaryLift_inclusionB f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhsB f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb)

/-- 概要：Q 成分の inclusionC 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_inclusionC {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (Cochain.ofHom (pushoutInclusionC f g)).comp (cofiberBoundaryLiftQ f g b hb)
      (zero_add (cofiberBoundaryDegree n + 1)) =
      (cofiberBoundaryDegree n).negOnePow • (cofiberBoundaryRhsC f g b hb) :=
  pushoutHomBoundaryLift_inclusionC f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhsB f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb)

/-- 概要：Q 成分の homotopy 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_homotopy {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (mappingCone.inl (cofiberDifference f g)).comp (cofiberBoundaryLiftQ f g b hb) (by omega) =
      (cofiberBoundaryDegree n).negOnePow •
        (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb) :=
  pushoutHomBoundaryLift_homotopy f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhsB f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb)

/-- 概要：Q 成分の diagonal 座標を実境界の残差で計算する。
方針：逆座標の評価式を実境界へ特殊化する。
規約：次数 q = −n−1。使われ方：残る四未知成分を零にする方程式。 -/
lemma cofiberBoundaryLiftQ_diagonal {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (Cochain.ofHom (pushoutDiagonal f g)).comp (cofiberBoundaryLiftQ f g b hb)
      (zero_add (cofiberBoundaryDegree n + 1)) =
      (cofiberBoundaryDegree n).negOnePow • ((Cochain.ofHom g).comp (cofiberBoundaryRhsC f g b hb)
        (zero_add (cofiberBoundaryDegree n + 1))) :=
  pushoutHomBoundaryLift_diagonal f g (cofiberBoundaryDegree n)
    (cofiberBoundaryRhsB f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsAB f g b hb - cofiberBoundaryRhsAC f g b hb)

end SerrePositivity.InfinityCategories
