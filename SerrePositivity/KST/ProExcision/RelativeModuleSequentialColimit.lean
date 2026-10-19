module
public import SerrePositivity.KST.ProExcision.RelativeModuleDiagram
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 実相対商と順序余極限の実同型

概要：有限段階の像の商の実余極限を、余極限の実写像の像の商と同定する。
方針：実相対商図式の余核の普遍性を余極限関手で写す。
規約：KST Proposition 4.14、SW92 Lemma 1.4。相対項の交換を仮定にしない。
使われ方：実安定相対ホモロジーへの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u r
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits
variable {R : Type r} [Ring R] {A B : ℕ ⥤ ModuleCat.{u} R}

/-- 概要：有限段階の実相対商の余極限と余極限の実相対商の実同型。
方針：実相対商の余核余錐を左随伴である実余極限関手で写し、実普遍性で比較する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。filtered 完全性の追加仮定も不要。
使われ方：安定 H_* の実比較と相対項の通常商の接続。 -/
def relativeModuleSequentialColimitIso (f : A ⟶ B) :
    relativeModule (colimMap f) ≅ colimit (relativeModuleDiagram f) :=
  (ModuleCat.cokernelIsColimit (colimMap f)).coconePointUniqueUpToIso
    ((relativeModuleDiagramCofork f).mapIsColimit (relativeModuleDiagramIsCokernel f)
      (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R))

end SerrePositivity.KST.ProExcision
