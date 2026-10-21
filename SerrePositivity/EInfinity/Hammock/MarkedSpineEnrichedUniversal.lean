module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedRestriction

/-!
# 元の指定因子と非指定生成矢による豊穣関手の普遍性

概要：任意の豊穣目標への拡張と元の二つの生成部分への制限は互いに逆である。
方針：元の単体写像の一意性と全関手の外延性を使う。
規約：対象写像と元の全 Hom の単体写像を保持する。
使われ方：自由積の豊穣普遍性の全単射。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D]

lemma EnrichedFoldData.ext {F G : EnrichedFoldData W D} (ho : F.obj = G.obj)
    (hm : HEq F.marked G.marked) (hg : HEq F.generator G.generator) : F = G := by
  cases F
  cases G
  cases ho
  cases eq_of_heq hm
  cases eq_of_heq hg
  rfl

lemma restrict_extend (F : EnrichedFoldData W D) :
    restrictEnrichedFunctor W F.enrichedFunctor = F := by
  apply EnrichedFoldData.ext (F := restrictEnrichedFunctor W F.enrichedFunctor) (G := F) rfl
  · exact heq_of_eq (funext fun X => funext fun Y => F.foldMap_marked X Y)
  · exact heq_of_eq (funext fun g => F.foldMap_generator g)

lemma extend_restrict :
    letI := enrichedCategory W
    ∀ G : EnrichedFunctor SSet.{u} (Paths C) D,
      (restrictEnrichedFunctor W G).enrichedFunctor = G := by
  let := enrichedCategory W
  intro G
  apply EnrichedFunctor.ext SSet.{u} (F := (restrictEnrichedFunctor W G).enrichedFunctor)
    (G := G) (fun _ => rfl)
  intro X Y
  have he := (restrictEnrichedFunctor W G).foldMap_unique G.map (fun _ _ => rfl)
    (fun _ => rfl) (fun X Y Z => G.map_comp X Y Z) X Y
  change (restrictEnrichedFunctor W G).foldMap X Y ≫
    𝟙 (G.obj X ⟶[SSet.{u}] G.obj Y) = G.map X Y
  exact (Category.comp_id ((restrictEnrichedFunctor W G).foldMap X Y)).trans he.symm

def enrichedFunctorEquiv (W : MorphismProperty C) :
    letI := enrichedCategory W
    EnrichedFunctor SSet.{u} (Paths C) D ≃ EnrichedFoldData W D := by
  letI := enrichedCategory W
  exact
    { toFun := restrictEnrichedFunctor W
      invFun := EnrichedFoldData.enrichedFunctor
      left_inv := extend_restrict
      right_inv := restrict_extend }

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
