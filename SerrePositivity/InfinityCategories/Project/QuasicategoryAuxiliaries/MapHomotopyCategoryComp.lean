module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

/-!
概要：単体的写像の合成が誘導するホモトピー圏の関手の合成則。
方針：Mathlib の `hoFunctor` の関手性に帰着する。
規約：公開名と名前空間を保ち、Mathlib のみに依存する。
使われ方：下降関手の相殺と他レーンのホモトピー圏の合成比較に用いる。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 単体的写像の合成が誘導するホモトピー圏の関手の合成則。 -/
lemma mapHomotopyCategory_comp_eq {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.mapHomotopyCategory (f ≫ g) =
      SSet.mapHomotopyCategory f ⋙ SSet.mapHomotopyCategory g := by
  change (hoFunctor.map (f ≫ g)).toFunctor = _
  rw [Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
