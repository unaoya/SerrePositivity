module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSections
public import SerrePositivity.InfinityCategories.Sheaves.SheafifyUnit

/-!
概要：層化後の大域切断を、指定した極限錐とともに定める。
方針：同じ層化関手の値に presentable 係数の小極限を適用する。
使われ方：HTT 6.2.2.7、Kerodon §7.1（Tag 02H1）の RΓ。
規約：任意の前層に定義し、層の単位との比較は元の単位を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 層化後の同じ前層の指定極限錐。 -/
def derivedGlobalSectionsCone (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C E) : JoinCone (sheafify J hJ F) :=
  globalSectionsCone _ (hasLimit_presheaf hE _)

/-- 指定錐の極限性。 -/
lemma derivedGlobalSectionsCone_isLimit (J : GrothendieckTopology C)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C E) : IsLimitCone (derivedGlobalSectionsCone J hJ hE F) :=
  globalSectionsCone_isLimit _ _

/-- 層化後の指定極限の頂点としての RΓ。 -/
def derivedGlobalSections (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C E) : E _⦋0⦌ :=
  (derivedGlobalSectionsCone J hJ hE F).vertex

/-- RΓ と指定錐の頂点は定義から一致する。 -/
lemma derivedGlobalSectionsCone_vertex (J : GrothendieckTopology C)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C E) :
    (derivedGlobalSectionsCone J hJ hE F).vertex = derivedGlobalSections J hJ hE F := rfl

end SerrePositivity.InfinityCategories.Sheaves
