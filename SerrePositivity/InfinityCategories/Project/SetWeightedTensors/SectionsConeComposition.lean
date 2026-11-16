module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：元の集合重みの射と全切断錐の制限は、元の合成を厳密に保つ。
方針：同じ mapElements の合成、nerve と持ち上げの関手性、joinMap の合成則を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存の錐の制限の法則。
使われ方：S8 の像への二段の制限を、元の射の指定切断比較へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
variable {I : Type u} [SmallCategory I] {P Q R : I ⥤ Type u}

/-- 元の圏の射に誘導される同じ単体集合の射は合成を保つ。 -/
lemma elementsMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    elementsMap (φ ≫ ψ) = elementsMap φ ≫ elementsMap ψ := by
  have h : (φ ≫ ψ).mapElements = φ.mapElements ⋙ ψ.mapElements := rfl
  have hn : nerveMap (φ.mapElements ⋙ ψ.mapElements) =
      nerveMap φ.mapElements ≫ nerveMap ψ.mapElements :=
    nerveFunctor.map_comp φ.mapElements.toCatHom ψ.mapElements.toCatHom
  change (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (φ ≫ ψ).mapElements) =
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap ψ.mapElements)
  rw [h, hn, CategoryTheory.Functor.map_comp]

/-- 元の二段の全錐の制限は、同じ合成射による全錐の制限と一致する。 -/
lemma restrictSectionsCone_comp {E : SSet.{u + 1}}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) (O : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c : JoinCone (diagram R O)) :
    restrictSectionsCone (φ ≫ ψ) O c =
      restrictSectionsCone φ O (restrictSectionsCone ψ O c) := by
  apply Subtype.ext
  change joinMap (𝟙 _) (elementsMap (φ ≫ ψ)) ≫ c.val =
    joinMap (𝟙 _) (elementsMap φ) ≫ (joinMap (𝟙 _) (elementsMap ψ) ≫ c.val)
  rw [elementsMap_comp, ← Category.assoc, ← joinMap_comp, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight
