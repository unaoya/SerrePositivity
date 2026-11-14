module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementPinchedFamily

/-!
# 指定 sourceIso による同じ全要素屋根の全関手比較

DAG XIII §2.2 の native な降下の補助。全複体の hammock の指定比較とその
sourceIso をそのまま使い、全パラメータの左脚の逆と評価を運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations (IsInvertibleEdge)
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma complexRelativeElementDerivedAugmentation_invertible
    (i : complexRelativeElementIndex A X Y) :
    IsInvertibleEdge ((nerve.edgeMk
      ((complexRelativeElementAugmentation A X Y).app i)).map
        (complexRelativeDerivedSource A)).toTruncated :=
  weakNerveEdges_inverts_arrows (complexRelativeCategory A) _
    (complexRelativeDerivedSource_inverts A) _ (complexRelativeElementAugmentation_weak A X Y i)

/-- 元の全要素の augmentation を既存の複体導来源で反転する全関手同型。 -/
def complexRelativeElementDerivedAugmentationIso :=
  NerveColumn.augmentationIso (complexRelativeDerivedSource A)
    (complexRelativeElementColumn A X Y) (complexRelativeElementAugmentation A X Y)
    (complexRelativeElementDerivedAugmentation_invertible A X Y)

/-- 指定 sourceIso は同じ全屋根と可換する。点ごとの π₀ の照合ではない。 -/
lemma complexRelativeElementSourceRoof_naturality :
    let V := complexRelativeElementColumn A X Y
    let p := complexRelativeElementAugmentation A X Y
    let s := complexRelativeElementEvaluation A X Y
    let hp := complexRelativeElementAugmentation_weak A X Y
    let K := complexHammockDerivedComparison A
    let e := complexHammockDerivedComparison_sourceIso A
    (e.precomp (nerveMap ((Functor.const _).obj ((complexRelativeUp A).obj X)))).hom ≫
      (complexRelativeElementDerivedAugmentationIso A X Y).inv ≫
        NerveColumn.hom (complexRelativeDerivedSource A) s =
      (NerveColumn.augmentationIso (complexHammockSource A ≫ K) V p
        (RoofPrefix.postcomp_augmentation_invertible (complexRelativeCategory A) V p hp K)).inv ≫
        NerveColumn.hom (complexHammockSource A ≫ K) s ≫
          (e.precomp (nerveMap ((Functor.const _).obj ((complexRelativeUp A).obj Y)))).hom :=
  NerveColumn.roof_naturality (complexHammockDerivedComparison_sourceIso A)
    (complexRelativeElementColumn A X Y) (complexRelativeElementAugmentation A X Y)
    (RoofPrefix.postcomp_augmentation_invertible (complexRelativeCategory A)
      (complexRelativeElementColumn A X Y) (complexRelativeElementAugmentation A X Y)
      (complexRelativeElementAugmentation_weak A X Y) (complexHammockDerivedComparison A))
    (complexRelativeElementDerivedAugmentation_invertible A X Y)
    (complexRelativeElementEvaluation A X Y)

end SerrePositivity.EInfinity.PowerOperation
