module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientExtension
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientSourceComparison

/-!
# 導来係数拡大と厳密な係数拡大の源

## 概要
HA §3.2.2 の底変更の導来関手を、厳密代数全体の上で比較する。

## 方針
元の関手的 cofibrant 置換に拡大を適用し、像の局所化源を比較する。

## 規約
厳密代数の底の複体の cofibrancy は仮定しない。

## 使われ方
M13 の導来底変更随伴の単位と余単位。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- DK 入力の係数拡大は、元の厳密代数への包含と可換。 -/
lemma cofibrantAlgebraDKCoefficientExtension_inclusion :
    nerveMap (cofibrantAlgebraDKCoefficientExtension f) ≫ cofibrantAlgebraInclusionNerve T =
      cofibrantAlgebraInclusionNerve S ≫ nerveMap (coefficientExtension f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ cofibrantAlgebraDKCoefficientExtension f) ⋙ cofibrantAlgebraDKInclusion T =
    (Γ ⋙ cofibrantAlgebraDKInclusion S) ⋙ coefficientExtension f
  rfl

/-- 元の厳密代数上での導来係数拡大は、同じ置換に厳密な拡大を施す。 -/
def barrattEcclesBaseChange_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraCAlgSource S ≫ barrattEcclesBaseChange f)
      (nerveMap (framedLimitProbeFunctor S ⋙ coefficientExtension f) ≫ algebraCAlgSource T) := by
  let Q := algebraCAlgReplacementNerve S
  let L := nerveMap (cofibrantAlgebraDKCoefficientExtension f)
  let e := (barrattEcclesBaseChange_cofibrantIso f).precomp Q
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (cAlgLocalizationSource_algebraIso T).symm (Q ≫ L)
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e ≪≫ ?_) (by rw [algebraCAlgSource, Category.assoc]) rfl
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d (Category.assoc _ _ _) ?_
  let i := cofibrantAlgebraInclusionNerve S
  let k := nerveMap (coefficientExtension f)
  let p := nerveMap (framedLimitProbeFunctor S)
  let z := algebraCAlgSource T
  have h : L ≫ cofibrantAlgebraInclusionNerve T = i ≫ k :=
    cofibrantAlgebraDKCoefficientExtension_inclusion f
  have h' : Q ≫ i = p := algebraCAlgReplacementNerve_inclusion S
  calc
    (Q ≫ L) ≫ cofibrantAlgebraInclusionNerve T ≫ z =
        (Q ≫ (L ≫ cofibrantAlgebraInclusionNerve T)) ≫ z := rfl
    _ = (Q ≫ (i ≫ k)) ≫ z := by rw [h]
    _ = (p ≫ k) ≫ z := by
      rw [← Category.assoc Q i k, h']
    _ = _ := rfl

end SerrePositivity.EInfinity.BarrattEccles
