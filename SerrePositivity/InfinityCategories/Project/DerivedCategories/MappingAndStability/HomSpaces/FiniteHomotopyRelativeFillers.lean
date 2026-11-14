module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofHomotopyRelativeFiller
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! # 有限対のホモトピー相対充填条件

概要：任意の有限単体集合対の厳密比較正方形に、全時刻整合的充填を持つ条件を表す。
方針：実屋根で証明した受入界面を一般の単体集合の射に対する述語へ束ねる。
規約：弱同値の定義とは区別する。使われ方：有限検査から Kan 置換の比較へ進む一般補題。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet

/-- 全ての有限対の厳密正方形に、全境界整合的なホモトピー相対充填が存在する。 -/
def HasFiniteHomotopyRelativeFillers {E Q : SSet.{u}} (F : E ⟶ Q) : Prop :=
  ∀ {L K : SSet.{u}} (i : L ⟶ K) [Mono i] [K.Finite] (a : L ⟶ E) (g : K ⟶ Q),
    a ≫ F = i ≫ g → Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofHomotopyRelativeFiller i F a g)

/-- 有限対の相対充填は、有限図式全体のホモトピー持ち上げを与える。 -/
lemma HasFiniteHomotopyRelativeFillers.finiteDiagramLift {E Q : SSet.{u}} {F : E ⟶ Q}
    (hF : HasFiniteHomotopyRelativeFillers F) {K : SSet.{u}} [K.Finite] (g : K ⟶ Q) :
    ∃ f : K ⟶ E, Nonempty (SSet.Homotopy (f ≫ F) g) := by
  let a : ((⊥ : K.Subcomplex) : SSet.{u}) ⟶ E := Subcomplex.isInitialBot.to E
  obtain ⟨H⟩ := hF (⊥ : K.Subcomplex).ι a g (Subcomplex.isInitialBot.hom_ext _ _)
  exact ⟨H.filler, ⟨H.comparison⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
