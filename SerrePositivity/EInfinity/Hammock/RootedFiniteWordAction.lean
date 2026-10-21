module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteProjection
public import SerrePositivity.EInfinity.Hammock.RelativeFixedWordAction
public import SerrePositivity.EInfinity.Hammock.Diagram

/-!
# 元の有限包の全語の作用と二方向の整合

概要：有限部分集合の包含と全体への射影が元の全語の作用と可換となる。
方針：既存の相対関手の固定端点での全語の自然性を使う。
規約：元の全列と全縦射を保持した厳密な関手の等式を使う。
使われ方：有限部分集合と Word の二変数の図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def wordActionFunctor (S : Finset Q) {a b : Word} (f : a ⟶ b) :
    termCategory T X Y a S ⥤ termCategory T X Y b S := by
  letI := FiniteQuiver.quiver (hull T X Y S)
  exact WordAction.functor f

lemma wordActionFunctor_id (S : Finset Q) (a : Word) :
    wordActionFunctor T X Y S (𝟙 a) = 𝟭 (termCategory T X Y a S) := by
  let := FiniteQuiver.quiver (hull T X Y S)
  exact WordAction.functor_id

lemma wordActionFunctor_comp (S : Finset Q) {a b c : Word} (f : a ⟶ b) (g : b ⟶ c) :
    wordActionFunctor T X Y S (f ≫ g) =
      wordActionFunctor T X Y S f ⋙ wordActionFunctor T X Y S g := by
  let := FiniteQuiver.quiver (hull T X Y S)
  exact WordAction.functor_comp f g

lemma mapFunctor_wordAction {S R : Finset Q} (h : S ⊆ R) {a b : Word} (f : a ⟶ b) :
    mapFunctor T X Y a h ⋙ wordActionFunctor T X Y R f =
      wordActionFunctor T X Y S f ⋙ mapFunctor T X Y b h := by
  let := FiniteQuiver.quiver (hull T X Y S)
  let := FiniteQuiver.quiver (hull T X Y R)
  exact Zigzag.Relative.wordAction_fixedFunctor_eq
    (FiniteQuiver.subsetRelative (QuiverTree.endpointHull_mono T X Y h)) rfl rfl f

lemma projectionFunctor_wordAction (S : Finset Q) {a b : Word} (f : a ⟶ b) :
    projectionFunctor T X Y a S ⋙ WordAction.functor f =
      wordActionFunctor T X Y S f ⋙ projectionFunctor T X Y b S := by
  let := FiniteQuiver.quiver (hull T X Y S)
  exact Zigzag.Relative.wordAction_fixedFunctor_eq (FiniteQuiver.pathRelative (hull T X Y S))
    rfl rfl f

end SerrePositivity.EInfinity.Hammock.RootedFinite
