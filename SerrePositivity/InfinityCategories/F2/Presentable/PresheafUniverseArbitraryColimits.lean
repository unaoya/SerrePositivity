module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseColimitShapeReduction
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseColimits

/-!
概要：指定された前層の宇宙変更は、任意の小さい添字の元の余極限全余錐を保存する。
方針：検証済みの coherent 添字での保存を、全余錐の形状置換による還元へ渡す。
規約：元の添字の quasicategory 性も sifted 性も追加しない。
使われ方：任意の小さい sifted 添字に対する P_Σ 延長の保存性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：元の前層の指定宇宙変更は、任意の小さい添字の指定全余錐の余極限性を保つ。
方針：検証済みの coherent 添字での保存を、全余錐の形状置換による還元へ渡す。
規約：元の添字の quasicategory 性も sifted 性も追加しない。
使われ方：任意の小さい sifted 添字に対する P_Σ 延長の保存性。 -/
lemma presheafUniverseDiagram_map_isColimit_arbitraryShape {I C : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafInfinity C)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (presheafUniverseDiagram C)
      (JoinCocone.ulift.{u + 1, u + 2} c)) :=
  mapUliftCocone_isColimit_of_quasicategoryShapes (presheafUniverseDiagram C)
    (fun _ _ D c hc => presheafUniverseDiagram_map_isColimit D c hc) D c hc

end SerrePositivity.InfinityCategories.HomotopyLimits
