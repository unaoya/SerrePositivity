module

public import SerrePositivity.KST.Spectra.PointedVerticalPathFunctoriality
public import Mathlib.Logic.Relation

/-!
概要：元の点つき射の垂直区間の有限鎖と、前後の合成・懸垂による移送。
方針：区間の実データの存在の反射推移閉包を取り、各区間の厳密な射影保持を移す。
規約：単一のホモトピーへの連結を仮定しない。使われ方：相対厳密化の帰納状態。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 全区間で元の射影を固定する、点つき射間の垂直区間の有限鎖。 -/
abbrev VerticalChain {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f g : T ⟶ E) : Prop :=
  Relation.ReflTransGen (fun f g ↦ Nonempty (VerticalPath p f g)) f g

namespace VerticalChain
variable {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}

/-- 有限鎖の両端は、元の射影へ戻すと厳密に同じ射。 -/
lemma endpoint_over (H : VerticalChain p f g) : g ≫ p = f ≫ p := by
  induction H with
  | refl => rfl
  | tail _ h ih =>
    obtain ⟨h⟩ := h
    exact h.endpoint_over.trans ih

/-- 垂直区間の有限鎖の両端は、元の点つき写像空間の同じ成分。 -/
lemma component (H : VerticalChain p f g) : componentOf f = componentOf g := by
  induction H with
  | refl => rfl
  | tail _ h ih =>
    obtain ⟨h⟩ := h
    exact ih.trans (π₀.sound h.edge)

/-- 元の後合成の厳密正方形は、垂直な有限鎖を保つ。 -/
lemma post (H : VerticalChain p f g) {E' B' : PointedSimplicialSet.{u}}
    (q : E' ⟶ B') (v : E ⟶ E') (w : B ⟶ B') (h : v ≫ q = p ≫ w) :
    VerticalChain q (f ≫ v) (g ≫ v) :=
  Relation.ReflTransGen.lift (fun f ↦ f ≫ v)
    (fun _ _ ⟨H⟩ ↦ ⟨H.post q v w h⟩) f g H

/-- 源の前合成は元の射影を固定した有限鎖を保つ。 -/
lemma pre (H : VerticalChain p f g) {U : PointedSimplicialSet.{u}} (i : U ⟶ T) :
    VerticalChain p (i ≫ f) (i ≫ g) :=
  Relation.ReflTransGen.lift (fun f ↦ i ≫ f) (fun _ _ ⟨H⟩ ↦ ⟨H.pre i⟩) f g H

/-- 懸垂は元の射影を固定した有限鎖を、懸垂した射影の有限鎖へ移す。 -/
lemma suspension (H : VerticalChain p f g) :
    VerticalChain (PointedSimplicialSet.circle.{u} ◁ p)
      (PointedSimplicialSet.circle.{u} ◁ f) (PointedSimplicialSet.circle.{u} ◁ g) :=
  Relation.ReflTransGen.lift (fun f ↦ PointedSimplicialSet.circle.{u} ◁ f)
    (fun _ _ ⟨H⟩ ↦ ⟨H.suspension⟩) f g H

end VerticalChain
end SerrePositivity.KST.Spectra.PointedMapping
