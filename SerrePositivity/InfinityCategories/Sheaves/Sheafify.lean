module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationReflection

/-!
概要：指定した反射の自己関手を層化として読み、その像が層であることを示す。
方針：反射像の所属を既存のlocalization_memから得る。
  文献対応：HTT 6.2.2.7、Kerodon Tag 06VH の層化反射。
規約：同じ反射の選択を全前層で用いる。反射の存在は後続の生成辺から供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 同じ反射の選択による前層圏の自己関手。 -/
def sheafificationFunctor (J : GrothendieckTopology C) (hJ : Sheafification J E) :
    PresheafCat C E ⟶ PresheafCat C E :=
  (Classical.choice hJ).localization

/-- 元の前層を同じ反射で層化する。 -/
def sheafify (J : GrothendieckTopology C) (hJ : Sheafification J E) (F : Presheaf C E) :
    Presheaf C E :=
  vertexToPresheaf ((sheafificationFunctor J hJ).app _ (functorVertex F))

/-- 指定した反射の像は、定義した層条件を満たす。 -/
lemma isSheaf_sheafify (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : IsSheaf J (sheafify J hJ F) :=
  (Classical.choice hJ).localization_mem (functorVertex F)

end SerrePositivity.InfinityCategories.Sheaves
