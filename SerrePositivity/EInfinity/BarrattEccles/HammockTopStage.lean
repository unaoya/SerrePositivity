module

public import SerrePositivity.EInfinity.BarrattEccles.HammockLengthFiltration
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStageColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordImageFactorization

/-!
# 任意の可換環上の交互方向の最大語による段階の表示

概要：前段階と最大長の交互方向語の図式で、元の長さ段階の余極限を回収する。
方針：元の全部分圏の Final な包含と、その標準の余極限比較を代入する。
規約：proper 性の追加入力は不要。段階の pushout の普遍性は後続。
使われ方：元の長さ段階の貼り合わせ。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

def algebraHammockTopStageDiagram (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage n ⥤ SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageDiagram (algebraHammockGraphDiagram A X Y) n

/-- 元の包含による、交互方向の最大語だけの図式の余極限と元の段階の同型。 -/
def algebraHammockTopStageColimitIso (n : ℕ) :
    colimit (algebraHammockTopStageDiagram A X Y n) ≅ algebraHammockLengthStage A X Y n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso (algebraHammockGraphDiagram A X Y) n

lemma algebraHammockTopStageColimitIso_fac (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage n) :
    colimit.ι (algebraHammockTopStageDiagram A X Y n) a ≫
        (algebraHammockTopStageColimitIso A X Y n).hom =
      algebraHammockLengthStageInclusion A X Y n a.obj.obj a.obj.property :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.topStageColimitIso_fac (algebraHammockGraphDiagram A X Y) n a

lemma algebraHammockTopStageColimitIso_toColimit_fac (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TopStage n) :
    (colimit.ι (algebraHammockTopStageDiagram A X Y n) a ≫
        (algebraHammockTopStageColimitIso A X Y n).hom) ≫
          algebraHammockLengthStageToColimit A X Y n =
      algebraHammockGraphInclusion A a.obj.obj X Y := by
  rw [algebraHammockTopStageColimitIso_fac, algebraHammockLengthStageInclusion_toColimit]

end SerrePositivity.EInfinity.BarrattEccles
