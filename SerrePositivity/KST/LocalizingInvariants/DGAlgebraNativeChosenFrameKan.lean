module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenMixedFrame
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeFrameKan

/-!
概要：選んだ実 right resolution の Hom と混合比較の標的を Kan 値関手に束ねる。
方針：元の rightFrameHom と同じ混合 Hom の関手的 Kan 置換を持ち上げる。
規約：全標的の元の射を保持し、AW frame に強い増大条件を要求しない。
使われ方：E2 の rightFrameHom と元の AW 模型の coherent な選択比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.F2
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def nativeCellChosenRightLargeKanFunctor : Mon (Complex R) ⥤ KanObject.{u + 1} where
  obj B := ⟨SSet.uliftFunctor.{u + 1, u}.obj
    ((nativeCellChosenRightMappingFunctor R A).obj B), by
      have := nativeCellChosenRightMapping_kanComplex R A B
      infer_instance⟩
  map f := SSet.uliftFunctor.{u + 1, u}.map
    ((nativeCellChosenRightMappingFunctor R A).map f)
  map_id B := (nativeCellChosenRightMappingFunctor R A ⋙
    SSet.uliftFunctor.{u + 1, u}).map_id B
  map_comp f g := (nativeCellChosenRightMappingFunctor R A ⋙
    SSet.uliftFunctor.{u + 1, u}).map_comp f g

def nativeCellChosenMixedReplacementLargeKanFunctor : Mon (Complex R) ⥤ KanObject.{u + 1} where
  obj B := ⟨SSet.uliftFunctor.{u + 1, u}.obj
    (continuousKanReplacement.obj ((nativeCellChosenMixedMappingFunctor R A).obj B)),
      inferInstance⟩
  map f := SSet.uliftFunctor.{u + 1, u}.map
    (continuousKanReplacement.map ((nativeCellChosenMixedMappingFunctor R A).map f))
  map_id B := (nativeCellChosenMixedMappingFunctor R A ⋙ continuousKanReplacement ⋙
    SSet.uliftFunctor.{u + 1, u}).map_id B
  map_comp f g := (nativeCellChosenMixedMappingFunctor R A ⋙ continuousKanReplacement ⋙
    SSet.uliftFunctor.{u + 1, u}).map_comp f g

lemma nativeCellChosenRightLargeKanFunctor_forget :
    nativeCellChosenRightLargeKanFunctor R A ⋙ kanObjectForget =
      nativeCellChosenRightMappingFunctor R A ⋙ SSet.uliftFunctor.{u + 1, u} := rfl

lemma nativeCellChosenMixedReplacementLargeKanFunctor_forget :
    nativeCellChosenMixedReplacementLargeKanFunctor R A ⋙ kanObjectForget =
      nativeCellChosenMixedMappingFunctor R A ⋙ continuousKanReplacement ⋙
        SSet.uliftFunctor.{u + 1, u} := rfl

def nativeCellChosenRightInfinityKanFunctor : InfinityPresentation R ⥤ KanObject.{u + 1} :=
  ULiftHom.down ⋙ nativeCellChosenRightLargeKanFunctor R A

def nativeCellChosenMixedReplacementInfinityKanFunctor :
    InfinityPresentation R ⥤ KanObject.{u + 1} :=
  ULiftHom.down ⋙ nativeCellChosenMixedReplacementLargeKanFunctor R A

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
