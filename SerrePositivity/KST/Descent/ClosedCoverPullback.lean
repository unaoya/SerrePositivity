module

public import SerrePositivity.KST.Descent.ClosedCoverGeometry
public import SerrePositivity.KST.Descent.FiniteTypeUniversal
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# 閉被覆の実際の引き戻しと比較立方体

## 概要
二つの閉部分の被覆を射の始域へ引き戻し、元の被覆の正方形への比較を構成する。

## 方針
第一射影の像の公式で被覆を移し、交わりへの射は引き戻しの普遍性で指定する。

## 規約
二重の交わりは実際の引き戻しであり、被約化や同型な代用品へ置き換えない。

## 使われ方
論文 補題 3.3・定理 3.1 の閉和に関する同変な降下比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V Y Z : FiniteTypeSchemes S}
variable (f : V ⟶ B) (i : Y ⟶ B) (j : Z ⟶ B)
variable [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left]

/-- 概要：二つの閉部分の被覆は任意の射への引き戻しで被覆を与える（論文 補題 3.3）。
方針：引き戻しの第一射影の像を元の像の逆像と同定する。
規約：スキームの点の引き戻しを集合の引き戻しと同一視しない。
使われ方：始域上の実際の二つの閉部分の抽象 blowup 正方形。 -/
theorem closedCoverPullback_covering
    (covering : Set.range i.hom.left ∪ Set.range j.hom.left = Set.univ) :
    Set.range (closedImmersionSquare f i).f₁₂.hom.left ∪
      Set.range (closedImmersionSquare f j).f₁₂.hom.left = Set.univ := by
  change Set.range (pullback.fst f.hom.left i.hom.left) ∪
    Set.range (pullback.fst f.hom.left j.hom.left) = Set.univ
  rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, ← Set.preimage_union,
    covering, Set.preimage_univ]

/-- 概要：引き戻した閉被覆の実際の交わりの正方形（論文 補題 3.3）。
方針：二つの第一射影を閉部分の包含として使う。
規約：右下の対象は元の射の始域 V。
使われ方：元の被覆の正方形と比較する列の幾何的入力。 -/
noncomputable def closedCoverPullbackSquare : Square (FiniteTypeSchemes S) := by
  exact @closedImmersionSquare S V (closedImmersionPullback f i)
    (closedImmersionPullback f j)
    (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂
    (closedImmersionSquare_first_isClosedImmersion f j)

/-- 概要：引き戻した閉被覆の交わりは有限型の圏内でも引き戻し（論文 補題 3.3）。
方針：実際の閉中心の引き戻しの普遍性を使う。
規約：比較の左上の指定対象を保持する。
使われ方：元の切断から交わりの比較射の切断を構成する。 -/
theorem closedCoverPullbackSquare_isPullback :
    IsPullback (closedCoverPullbackSquare f i j).f₁₂ (closedCoverPullbackSquare f i j).f₁₃
      (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂ :=
  @closedImmersionSquare_isPullback S V (closedImmersionPullback f i)
    (closedImmersionPullback f j) (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂
    (closedImmersionSquare_first_isClosedImmersion f j)

/-- 概要：引き戻した閉被覆を実際の抽象 blowup とする（論文 補題 3.3）。
方針：始域の被約性と引き戻した被覆に閉和の構成を適用する。
規約：引き戻した二つの部分と交わりの被約性は要求しない。
使われ方：始域の閉和に対する自然な長完全列。 -/
noncomputable def closedCoverPullbackBlowup [IsReduced V.obj.left]
    (covering : Set.range i.hom.left ∪ Set.range j.hom.left = Set.univ) :
    AbstractBlowupSquare S := by
  exact @closedCoverAbstractBlowup S V (closedImmersionPullback f i)
    (closedImmersionPullback f j) inferInstance
    (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂
    (closedImmersionSquare_first_isClosedImmersion f i)
    (closedImmersionSquare_first_isClosedImmersion f j)
    (closedCoverPullback_covering f i j covering)

/-- 概要：交わりの二つの射影を元の閉部分へ送る射は基底上で可換（論文 補題 3.3）。
方針：二つの中心の正方形と、引き戻した閉被覆の正方形の可換性を合成する。
規約：元の交わりへの持ち上げの指定条件。
使われ方：比較立方体の左上の射の構成。 -/
theorem closedCoverPullbackIntersection_fac :
    ((closedCoverPullbackSquare f i j).f₁₂ ≫ (closedImmersionSquare f i).f₁₃) ≫ i =
      ((closedCoverPullbackSquare f i j).f₁₃ ≫ (closedImmersionSquare f j).f₁₃) ≫ j := by
  calc
    _ = ((closedCoverPullbackSquare f i j).f₁₂ ≫ (closedImmersionSquare f i).f₁₂) ≫ f := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k ↦ (closedCoverPullbackSquare f i j).f₁₂ ≫ k)
          (closedImmersionSquare f i).fac.symm).trans (Category.assoc _ _ _).symm)
    _ = ((closedCoverPullbackSquare f i j).f₁₃ ≫ (closedImmersionSquare f j).f₁₂) ≫ f :=
      congrArg (fun k ↦ k ≫ f) (closedCoverPullbackSquare f i j).fac
    _ = ((closedCoverPullbackSquare f i j).f₁₃ ≫ (closedImmersionSquare f j).f₁₃) ≫ j :=
      (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (closedCoverPullbackSquare f i j).f₁₃ ≫ k)
        (closedImmersionSquare f j).fac).trans (Category.assoc _ _ _).symm)

/-- 概要：引き戻した閉被覆から元の閉被覆への実際の比較立方体（論文 補題 3.3）。
方針：三頂点では f と中心の射影を使い、交わりでは実際の引き戻しへ持ち上げる。
規約：四つの面の可換性を射の等式で保持する。
使われ方：閉和の全次数列を引き戻しで比較する。 -/
noncomputable def closedCoverPullbackCube : closedCoverPullbackSquare f i j ⟶
    closedImmersionSquare i j where
  τ₁ := closedImmersionPullbackLift i j
    ((closedCoverPullbackSquare f i j).f₁₂ ≫ (closedImmersionSquare f i).f₁₃)
    ((closedCoverPullbackSquare f i j).f₁₃ ≫ (closedImmersionSquare f j).f₁₃)
    (closedCoverPullbackIntersection_fac f i j)
  τ₂ := (closedImmersionSquare f i).f₁₃
  τ₃ := (closedImmersionSquare f j).f₁₃
  τ₄ := f
  comm₁₂ := (closedImmersionPullbackLift_fst i j _ _ _).symm
  comm₁₃ := (closedImmersionPullbackLift_snd i j _ _ _).symm
  comm₂₄ := (closedImmersionSquare f i).fac
  comm₃₄ := (closedImmersionSquare f j).fac

end SerrePositivity.KST.Descent
