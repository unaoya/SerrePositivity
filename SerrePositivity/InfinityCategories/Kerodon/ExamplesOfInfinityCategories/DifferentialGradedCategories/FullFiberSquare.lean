module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullPullbackReflection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberPullback

/-! # 充満 dg 部分圏内の標準 fiber 四角形

概要：B,C,D と標準 fiber が部分圏に属せば、標準 fiber 四角形は部分圏内の ∞ 引き戻しになる。
方針：二つの標準三角形を部分圏へ持ち上げて貼り、周囲の引き戻し性を反映する。
規約：HTT §1.2.13、HA §1.3.1。使われ方：fiber で閉じた部分圏、特に Semifree への制限。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] (P : Complex A → Prop) {B C D : Complex A}

/-- 概要：P 内の標準 fiber の上三角形を部分圏の単体へ持ち上げる。
方針：三頂点 P,C,D にそれぞれの所属の証明を添え、Hom 成分は変えない。
規約：HA Construction 1.3.1.6。使われ方：部分圏の標準四角形の第一セル。 -/
def fullFiberUpperTriangle (g : B ⟶ D) (h : C ⟶ D)
    (hC : P C) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFullSubcategory (Complex A) P) 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull A (Complex A) P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).simplex (fun i => by
    fin_cases i
    · exact hP
    · exact hC
    · exact hD)

/-- 概要：P 内の標準 fiber の下三角形を部分圏の単体へ持ち上げる。
方針：三頂点 P,B,D にそれぞれの所属の証明を添え、Hom 成分は変えない。
規約：HA Construction 1.3.1.6。使われ方：部分圏の標準四角形の第二セル。 -/
def fullFiberLowerTriangle (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFullSubcategory (Complex A) P) 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull A (Complex A) P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).simplex (fun i => by
    fin_cases i
    · exact hP
    · exact hB
    · exact hD)

/-- 概要：部分圏へ持ち上げた標準の二三角形は対角で一致する。
方針：包含の単射性で周囲へ戻し、標準三角形の対角の式を使う。
規約：HTT §1.2.13。使われ方：部分圏内の四角形の貼合せ。 -/
lemma fullFiberTriangles_compatible (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hC : P C) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
        (SSet.yonedaEquiv.symm (fullFiberUpperTriangle P g h hC hD hP) :
          (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (Complex A) P)) =
      SSet.stdSimplex.δ (1 : Fin 3) ≫
        SSet.yonedaEquiv.symm (fullFiberLowerTriangle P g h hB hD hP) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) P))).1
  simp only [Category.assoc, fullFiberUpperTriangle, fullFiberLowerTriangle,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull_yoneda_inclusion]
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).d₁, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).d₁]

/-- 概要：標準 fiber の四頂点が P を満たすと、四角形を充満部分圏内に構成できる。
方針：上・下三角形を部分圏へ持ち上げ、対角に沿った押し出しで貼る。
規約：HTT §1.2.13。使われ方：閉性の定理から部分圏の引き戻しを作る。 -/
def fullFiberSquare (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hC : P C) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (Complex A) P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm (fullFiberUpperTriangle P g h hC hD hP))
    (SSet.yonedaEquiv.symm (fullFiberLowerTriangle P g h hB hD hP))
    (fullFiberTriangles_compatible P g h hB hC hD hP)

/-- 概要：部分圏内の標準四角形の包含像は周囲の標準 fiber 四角形に等しい。
方針：二三角形の押し出しによる外延性と liftToFull の包含像の公式を使う。
規約：HTT §1.2.13。使われ方：周囲の引き戻し性を部分圏へ戻す。 -/
lemma fullFiberSquare_inclusion (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hC : P C) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    fullFiberSquare P g h hB hC hD hP ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) P) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc _ _ _) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_upper]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull_yoneda_inclusion A (Complex A) P _ _
  · rw [← Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc _ _ _) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_lower]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.liftToFull_yoneda_inclusion A (Complex A) P _ _

/-- 概要：fiber が部分圏に属する標準 fiber 四角形は部分圏の dg nerve の ∞ 引き戻し。
方針：包含像を周囲の標準四角形に同定し、N7c の引き戻し性を充満部分圏へ反映する。
規約：HTT §1.2.13。使われ方：fiber と有限直和で閉じた部分圏、特に Semifree の引き戻し。 -/
lemma fullFiberSquare_isPullback (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hC : P C) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (fullFiberSquare P g h hB hC hD hP) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isPullbackSquare_of_fullInclusion A (Complex A) P
  rw [fullFiberSquare_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_isPullback g h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
