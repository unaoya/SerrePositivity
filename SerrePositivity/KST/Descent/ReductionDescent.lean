module

public import SerrePositivity.KST.Descent.FiniteTypeReduction
public import SerrePositivity.KST.Descent.DescentNaturality

/-!
# 定理 3.1 の一般から被約への還元

## 概要
Noether な基底上の有限型対象の射について、全次数の降下比較と
その被約化の全次数の降下比較が同値であることを証明する。

## 方針
実際の被約化関手の自然性で同変正方形を構成し、公理 (3) を二つの包含に適用する。
不変部分への比較の全単射性も元の同変引き戻しの全単射性から証明する。

## 規約
前層 L の冪零不変性は明示的な仮定。
幾何的推移性や有限全射降下の結論は、この還元の仮定に含めない。

## 使われ方
論文 補題 3.3・定理 3.1 の「整 → 被約 → 一般」の最後の移行。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y : FiniteTypeSchemes S} {G : Type*} [Group G]

/-- 概要：基底上の群作用は reduction 上でも被約化した射の上にある（論文 (3.7)）。
方針：元の可換式に reduction 関手を適用する。
規約：reduction 後の基底は Y_red であり、元の Y に留めない。
使われ方：被約化した射の降下比較の定義。 -/
theorem finiteTypeReductionAction_over_base (f : X ⟶ Y) (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) (g : G) :
    (finiteTypeReductionAction action g).asIso.hom ≫ finiteTypeReductionMap f =
      finiteTypeReductionMap f := by
  change (finiteTypeReductionFunctor S).map (action g).asIso.hom ≫
      (finiteTypeReductionFunctor S).map f = (finiteTypeReductionFunctor S).map f
  rw [← Functor.map_comp, over_base]

/-- 概要：Noether 基底上の全次数の降下は被約化後の降下と同値（論文 定理 3.1）。
方針：被約化の同変正方形の両包含に公理 (3) を適用して指定比較を移す。
規約：不変部分・任意の係数・負次数を含む全整数次数を保持する。
使われ方：「一般 → 被約」の還元。主定理の被約な場合の証明は別に必要。 -/
theorem Nilinvariant.piDescent_iff_reduction [IsNoetherian S] {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient) [Nilinvariant S L]
    (f : X ⟶ Y) (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) :
    L.PiDescent f action over_base ↔
      L.PiDescent (finiteTypeReductionMap f) (finiteTypeReductionAction action)
        (finiteTypeReductionAction_over_base f action over_base) := by
  apply L.piDescent_iff_of_bijective_square f (finiteTypeReductionMap f)
    (finiteTypeReductionInclusion X) (finiteTypeReductionInclusion Y)
    (finiteTypeReductionMap_comp_inclusion f).symm action (finiteTypeReductionAction action)
    over_base (finiteTypeReductionAction_over_base f action over_base)
    (finiteTypeReductionAction_comp_inclusion action)
  · exact Nilinvariant.noetherianReduction_pullback_bijective L X
  · exact Nilinvariant.noetherianReduction_pullback_bijective L Y

end SerrePositivity.KST.Descent
