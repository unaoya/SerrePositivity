module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftElements
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.NerveHomUniverseIso

/-!
概要：宇宙を持ち上げた通常の要素圏の反対nerveを、元の反対要素圏のnerveへ戻す。
方針：同じ単体のULiftとHomのULiftを上下し、両方の厳密な往復を照合する。
規約：元の次数と全単体作用素を保持する。一般の大きい単体集合を小さくする構成ではない。
使われ方：元のnative fiberの反対要素圏から、元のleft-roof比較の入力への係数移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
variable (K : SSet.{v})

/-- 同じ元の単体をdownして、Homの宇宙だけを保持した反対要素圏へ送る。 -/
def elementsOppositeUniverseIndex :
    (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ⥤
      ULiftHom.{max w v} K.Elementsᵒᵖ :=
  (ULiftHom.down.{0,max w v,max w v} ⋙ downElements.{w,v} K).op ⋙
    ULiftHom.up.{0,v,max w v}

/-- 元の同じ単体をupして、持ち上げた通常の要素圏の反対圏へ戻す。 -/
def elementsOppositeUniverseIndexInverse :
    ULiftHom.{max w v} K.Elementsᵒᵖ ⥤
      (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ :=
  ULiftHom.down.{0,v,max w v} ⋙
    (upElements.{w,v} K ⋙ ULiftHom.up.{0,max w v,max w v}).op

/-- 元の同じ上下の全射列からなる、反対要素圏のnerveの厳密な同型。 -/
def elementsOppositeUniverseNerveIso :
    nerve (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ≅
      nerve (ULiftHom.{max w v} K.Elementsᵒᵖ) := by
  let f : nerve (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ⟶
      nerve (ULiftHom.{max w v} K.Elementsᵒᵖ) :=
    { app _ := ↾fun σ => σ ⋙ elementsOppositeUniverseIndex.{w,v} K
      naturality _ _ _ := rfl }
  let g : nerve (ULiftHom.{max w v} K.Elementsᵒᵖ) ⟶
      nerve (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ :=
    { app _ := ↾fun σ => σ ⋙ elementsOppositeUniverseIndexInverse.{w,v} K
      naturality _ _ _ := rfl }
  refine ⟨f, g, ?_, ?_⟩
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
