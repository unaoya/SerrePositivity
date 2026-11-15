module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：層条件と層の頂点条件を、元の全関手同型に沿って運ぶ。
方針：指定した篩錐全体へ同じ同型を前合成し、極限性を移す。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の全錐比較、site の同値の輸送。
規約：対象ごとの同型だけを仮定せず、全関手の同型を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の篩錐の全関手同型により層条件を移す。 -/
lemma IsSheaf.of_functorIso {J : GrothendieckTopology C} {F G : Presheaf C E}
    (hF : IsSheaf J F) (e : FunctorIso F G) : IsSheaf J G := by
  intro U S hS
  exact (hF U S hS).of_functorIso (e.precomp ((nerveCone (sieveCone S)).ulift).val)

/-- 全前層の同じ同型は層であることを保存し反映する。 -/
lemma isSheaf_iff_of_functorIso (J : GrothendieckTopology C) {F G : Presheaf C E}
    (e : FunctorIso F G) : IsSheaf J F ↔ IsSheaf J G :=
  ⟨fun h ↦ h.of_functorIso e, fun h ↦ h.of_functorIso e.symm⟩

/-- 前層圏の頂点の同型に沿って層の頂点条件を運ぶ。 -/
lemma sheafProperty_iff_of_vertexIso (J : GrothendieckTopology C)
    {F G : (PresheafCat C E) _⦋0⦌} (e : VertexIso F G) :
    sheafProperty J F ↔ sheafProperty J G := by
  let e' : FunctorIso (vertexToPresheaf F) (vertexToPresheaf G) :=
    eqToIso (congrArg HomotopyCategory.mk ((functorVertexEquiv _ _).apply_symm_apply F)) ≪≫
      e ≪≫ (eqToIso (congrArg HomotopyCategory.mk
        ((functorVertexEquiv _ _).apply_symm_apply G))).symm
  exact isSheaf_iff_of_functorIso J e'

end SerrePositivity.InfinityCategories.Sheaves
