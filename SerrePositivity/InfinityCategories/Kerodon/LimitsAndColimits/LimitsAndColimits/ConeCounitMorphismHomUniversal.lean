module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitMorphismNaturality
public import Mathlib.CategoryTheory.HomCongr

/-!
概要：頂点で可逆な全錐の変換に沿って、元の余単位の Hom 判定を比較する。
方針：実際の余単位の自然性を、同じ頂点射による Hom 全単射と合成する。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の指定三角形と降下。
規約：全錐間の射と底での実際の変換を保持する。極限存在はまだ結論しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ頂点射を経由することで、底の変換との合成による Hom 判定を輸送する。 -/
lemma coneCounitHom_comp_bijective_iff {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (c : JoinCone p) (d : JoinCone q) (α : FunctorHom c.val d.val)
    [IsIso (functorHomEvaluate α (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)))]
    (y : X _⦋0⦌) :
    Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk c.vertex => constantFunctorHomMap K β ≫ coneCounitHom c ≫
        kanFunctorHomCongr c.property d.property
          ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map α)) ↔
    Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex => constantFunctorHomMap K β ≫ coneCounitHom d) := by
  let g : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex :=
    functorHomEvaluate α (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))
  have hg : Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk c.vertex => β ≫ g) := by
    convert (Iso.homCongr (Iso.refl (SSet.HomotopyCategory.mk y)) (asIso g)).bijective using 1
    funext β
    simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, asIso_hom]
  have hn : constantFunctorHomMap K g ≫ coneCounitHom d = coneCounitHom c ≫
      kanFunctorHomCongr c.property d.property
        ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map α) :=
    coneCounitHom_morphism_naturality c d α
  have he : (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex => constantFunctorHomMap K β ≫ coneCounitHom d) ∘
      (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
        SSet.HomotopyCategory.mk c.vertex => β ≫ g) =
      (fun β => constantFunctorHomMap K β ≫ coneCounitHom c ≫
        kanFunctorHomCongr c.property d.property
          ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map α)) := by
    funext β
    simp only [Function.comp_apply, constantFunctorHomMap_comp, Category.assoc]
    rw [hn]
  have h := Function.Bijective.of_comp_iff
    (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex => constantFunctorHomMap K β ≫ coneCounitHom d) hg
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
