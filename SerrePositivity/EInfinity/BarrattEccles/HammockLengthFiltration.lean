module

public import SerrePositivity.EInfinity.BarrattEccles.HammockReducedColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthNaturality

/-!
# 任意の可換環上の元の hammock の長さ濾過

概要：元の全語の図式の長さ段階、Nat 図式、余極限と縮約 hammock への同型を提供する。
方針：同じ固定語の標準射を保つ長さ濾過の普遍性を実際の E 代数へ代入する。
規約：段階の単射性・貼り合わせ・弱同値不変性は後続。係数環は任意。
使われ方：元の三列の標準射の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

def algebraHammockLengthStage (n : ℕ) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage (algebraHammockGraphDiagram A X Y) n

def algebraHammockLengthStageInclusion (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : a.length ≤ n) :
    algebraHammockGraph A a X Y ⟶ algebraHammockLengthStage A X Y n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion (algebraHammockGraphDiagram A X Y) n a ha

def algebraHammockLengthTransition {n m : ℕ} (h : n ≤ m) :
    algebraHammockLengthStage A X Y n ⟶ algebraHammockLengthStage A X Y m :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition (algebraHammockGraphDiagram A X Y) h

def algebraHammockLengthDiagram : ℕ ⥤ SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthDiagram (algebraHammockGraphDiagram A X Y)

def algebraHammockLengthStageToColimit (n : ℕ) :
    algebraHammockLengthStage A X Y n ⟶ algebraHammockColimitGraph A X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageToColimit (algebraHammockGraphDiagram A X Y) n

lemma algebraHammockLengthStageInclusion_toColimit (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (ha : a.length ≤ n) :
    algebraHammockLengthStageInclusion A X Y n a ha ≫
        algebraHammockLengthStageToColimit A X Y n = algebraHammockGraphInclusion A a X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_toColimit (algebraHammockGraphDiagram A X Y) n a ha

/-- 元の長さ制限段階の反復余極限と、同じ全語の余極限の同型。 -/
def algebraHammockLengthColimitIso :
    colimit (algebraHammockLengthDiagram A X Y) ≅ algebraHammockColimitGraph A X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso (algebraHammockGraphDiagram A X Y)

lemma algebraHammockLengthColimitIso_fac (n : ℕ) :
    colimit.ι (algebraHammockLengthDiagram A X Y) n ≫
        (algebraHammockLengthColimitIso A X Y).hom = algebraHammockLengthStageToColimit A X Y n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthColimitIso_fac (algebraHammockGraphDiagram A X Y) n

lemma algebraHammockLengthColimitIso_word_fac (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : a.length ≤ n) :
    algebraHammockLengthStageInclusion A X Y n a ha ≫
        colimit.ι (algebraHammockLengthDiagram A X Y) n ≫
          (algebraHammockLengthColimitIso A X Y).hom = algebraHammockGraphInclusion A a X Y := by
  rw [algebraHammockLengthColimitIso_fac, algebraHammockLengthStageInclusion_toColimit]

/-- 同じ元の標準射で定まる、長さ濾過の余極限と縮約済み hammock の同型。 -/
def algebraHammockLengthReducedIso :
    colimit (algebraHammockLengthDiagram A X Y) ≅ algebraHammockReducedSimplicialSet A X Y :=
  (algebraHammockLengthColimitIso A X Y).trans (algebraHammockReducedColimitIso A X Y)

lemma algebraHammockLengthReducedIso_word_fac (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : a.length ≤ n) :
    algebraHammockLengthStageInclusion A X Y n a ha ≫
        colimit.ι (algebraHammockLengthDiagram A X Y) n ≫
          (algebraHammockLengthReducedIso A X Y).hom =
      algebraHammockGraphNormalization A X Y a := by
  change algebraHammockLengthStageInclusion A X Y n a ha ≫
      colimit.ι (algebraHammockLengthDiagram A X Y) n ≫
        ((algebraHammockLengthColimitIso A X Y).hom ≫
          (algebraHammockReducedColimitIso A X Y).hom) = _
  rw [← Category.assoc (colimit.ι (algebraHammockLengthDiagram A X Y) n)
    (algebraHammockLengthColimitIso A X Y).hom (algebraHammockReducedColimitIso A X Y).hom,
    algebraHammockLengthColimitIso_fac, ← Category.assoc,
    algebraHammockLengthStageInclusion_toColimit, algebraHammockReducedColimitIso_hom_fac]

end SerrePositivity.EInfinity.BarrattEccles
