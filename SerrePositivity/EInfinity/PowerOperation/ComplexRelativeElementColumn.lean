module

public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockSource
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram

/-!
# 正規化テンソルの同じ全要素屋根を全複体の相対圏へ送る

DAG XIII §2.2 の native な降下への前段。宇宙の表示だけを合わせ、同じ鎖写像・
augmentation・評価・全パラメータを保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev complexRelativeUp : Complex A ⥤ (complexRelativeCategory A).category :=
  AsSmall.up.{u, u + 1, u + 1}

abbrev complexRelativeElementIndex : Type (u + 1) :=
  ULiftHom.{u + 1} (normalizedTensorElementIndex A X Y)

def complexRelativeElementColumn : complexRelativeElementIndex A X Y ⥤
    (complexRelativeCategory A).category :=
  ULiftHom.down.{u, u + 1, u + 1} ⋙ normalizedTensorElementDiagram A X Y ⋙ complexRelativeUp A

def complexRelativeElementAugmentation : complexRelativeElementColumn A X Y ⟶
    (Functor.const _).obj ((complexRelativeUp A).obj X) :=
  Functor.whiskerLeft ULiftHom.down.{u, u + 1, u + 1}
    (Functor.whiskerRight (normalizedTensorElementAugmentation A X Y) (complexRelativeUp A))

def complexRelativeElementEvaluation : complexRelativeElementColumn A X Y ⟶
    (Functor.const _).obj ((complexRelativeUp A).obj Y) :=
  Functor.whiskerLeft ULiftHom.down.{u, u + 1, u + 1}
    (Functor.whiskerRight (normalizedTensorElementEvaluation A X Y) (complexRelativeUp A))

lemma complexRelativeElementAugmentation_weak (s : complexRelativeElementIndex A X Y) :
    (complexRelativeCategory A).weakEquivalences
      ((complexRelativeElementAugmentation A X Y).app s) :=
  normalizedTensorElementAugmentation_quasiIso A X Y (ULiftHom.objDown s)

lemma complexRelativeElementColumn_map_weak {s t : complexRelativeElementIndex A X Y}
    (f : s ⟶ t) :
    (complexRelativeCategory A).weakEquivalences
      ((complexRelativeElementColumn A X Y).map f) :=
  normalizedTensorElementDiagram_map_quasiIso A X Y (ULiftHom.down.map f)

end SerrePositivity.EInfinity.PowerOperation
