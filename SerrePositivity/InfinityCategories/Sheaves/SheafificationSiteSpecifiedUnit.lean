module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationSiteSpecifiedComparison

/-!
概要：site 同値に沿う指定層化比較が、元の二つの層化単位を保つことを示す。
方針：元の包含の正方形と同じ横の mate の逆に、既存の全二胞体の単位法則を適用する。
  文献対応：HTT 6.2.2.7、Kerodon §6.2（Tag 02EH）の指定反射の輸送。
規約：元の hJ・hK の単位、同じ包含の正方形、同じ全関手比較を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

local instance sheafificationSiteSpecifiedUnitHomCategory (A B : SSet.QCat.{u + 1}) :
    Category.{u + 1} (A ⟶ B) := SSet.QCat.bicategory.homCategory A B

/-- 指定全関手比較の二胞体の合成は、元の層化単位の全自然な正方形を可換にする。 -/
lemma sheafificationReindexSpecified_unit (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (hJ : Sheafification J E) (hK : Sheafification K E) :
    let T := reindexPresheafFunctor (E := E) e.functor
    let S := reindexSheafFunctor (E := E) e J K hf
    let rJ := Classical.choice hJ
    let rK := Classical.choice hK
    let j : qcatMap rJ.reflector ⊣ qcatMap (sheafInclusion J) := rJ.adjunction
    let k : qcatMap rK.reflector ⊣ qcatMap (sheafInclusion K) := rK.adjunction
    let β : qcatMap (sheafInclusion K) ≫ qcatMap T ≅
        qcatMap S ≫ qcatMap (sheafInclusion J) :=
      functorIsoToQcatIso (sheafInclusionReindexIso e J K hf)
    let α : qcatMap T ≫ qcatMap rJ.reflector ≅ qcatMap rK.reflector ≫ qcatMap S :=
      sheafificationReindexSpecifiedMateIso e J K hf hg hJ hK
    𝟙 (qcatMap T) ⊗≫ k.unit ▷ qcatMap T ⊗≫ qcatMap rK.reflector ◁ β.hom ⊗≫
        α.inv ▷ qcatMap (sheafInclusion J) ⊗≫
        𝟙 (qcatMap T ≫ (qcatMap rJ.reflector ≫ qcatMap (sheafInclusion J))) =
      𝟙 (qcatMap T) ⊗≫ qcatMap T ◁ j.unit ⊗≫
        𝟙 (qcatMap T ≫ (qcatMap rJ.reflector ≫ qcatMap (sheafInclusion J))) := by
  dsimp only
  let t := (reindexPresheafFunctor_isQCatEquivalence (E := E) e).choose
  let s := (reindexSheafFunctor_isQCatEquivalence (E := E) e J K hf hg).choose
  haveI : IsIso (equivalenceAdjunction t).unit := equivalenceAdjunction_unit_isIso t
  haveI : IsIso (equivalenceAdjunction s).counit := equivalenceAdjunction_counit_isIso s
  exact equivalenceSquareMateIso_inverse_unit
    (l₁ := qcatMap (Classical.choice hK).reflector)
    (r₁ := qcatMap (sheafInclusion K))
    (l₂ := qcatMap (Classical.choice hJ).reflector)
    (r₂ := qcatMap (sheafInclusion J))
    (f₁ := qcatMap (reindexPresheafFunctor e.functor))
    (f₂ := qcatMap (reindexSheafFunctor e J K hf)) (Classical.choice hK).adjunction
    (Classical.choice hJ).adjunction (equivalenceAdjunction t) (equivalenceAdjunction s)
    (functorIsoToQcatIso (sheafInclusionReindexIso e J K hf))

end SerrePositivity.InfinityCategories.Sheaves
