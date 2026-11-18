module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.UniversalProperty
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom

/-!
概要：右 Kan の指定余単位との合成は、定値頂点からの Hom 判定を保ち反映する。
方針：同じ右 Kan Hom 全単射と端点の移送を合成し、定値関手の前合成則を使う。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の極限の合成。
規約：π₀ の Hom の法則であり、これ単独で極限性を定義しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 指定右 Kan 射による Hom 比較を、同じ定値頂点へ正規化する。 -/
lemma rightKanHomMap_constant_bijective {I K X : SSet.{u}} (δ : I ⟶ K)
    {p : K ⟶ X} {q : I ⟶ X} (α : FunctorHom (δ ≫ p) q)
    (hα : RightKanHomUniversal δ α) (y : X _⦋0⦌) :
    Function.Bijective (fun η : FunctorHom (SSet.const y) p =>
      kanFunctorHomCongr (V := q) (SSet.comp_const δ y) rfl
        (rightKanHomMap δ α (SSet.const y) η)) :=
  (kanFunctorHomCongr (V := q) (SSet.comp_const δ y) rfl).bijective.comp
    (hα (SSet.const y))

/-- 定値頂点からの元の射と、指定右 Kan 余単位との合成の分配則。 -/
lemma rightKanHomMap_constant_comp {I K X : SSet.{u}} (δ : I ⟶ K)
    {p : K ⟶ X} {q : I ⟶ X} (α : FunctorHom (δ ≫ p) q)
    {y v : X _⦋0⦌} (β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk v) (ε : FunctorHom (SSet.const v) p) :
    kanFunctorHomCongr (V := q) (SSet.comp_const δ y) rfl
      (rightKanHomMap δ α (SSet.const y) (constantFunctorHomMap K β ≫ ε)) =
    constantFunctorHomMap I β ≫
      kanFunctorHomCongr (V := q) (SSet.comp_const δ v) rfl
        (rightKanHomMap δ α (SSet.const v) ε) := by
  have he : (hoFunctor.map ((pre δ).app X)).toFunctor.map (constantFunctorHomMap K β) =
      constantFunctorHomMap I β := constantFunctorHomMap_precomp δ β
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id, rightKanHomMap, Functor.map_comp,
    Category.assoc]
  rw [he]

/-- 元の Hom 判定の全単射性は、同じ指定右 Kan 余単位で合成した後と同値。 -/
lemma rightKanCounitHom_bijective_iff {I K X : SSet.{u}} (δ : I ⟶ K)
    {p : K ⟶ X} {q : I ⟶ X} (α : FunctorHom (δ ≫ p) q)
    (hα : RightKanHomUniversal δ α) (v y : X _⦋0⦌)
    (ε : FunctorHom (SSet.const v) p) :
    Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk v => constantFunctorHomMap K β ≫ ε) ↔
    Function.Bijective (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk v => constantFunctorHomMap I β ≫
        kanFunctorHomCongr (V := q) (SSet.comp_const δ v) rfl
          (rightKanHomMap δ α (SSet.const v) ε)) := by
  have hb := (rightKanHomMap_constant_bijective δ α hα y).of_comp_iff'
    (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk v => constantFunctorHomMap K β ≫ ε)
  have he : (fun η : FunctorHom (SSet.const y) p =>
      kanFunctorHomCongr (V := q) (SSet.comp_const δ y) rfl
        (rightKanHomMap δ α (SSet.const y) η)) ∘
      (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
        SSet.HomotopyCategory.mk v => constantFunctorHomMap K β ≫ ε) =
      (fun β => constantFunctorHomMap I β ≫
        kanFunctorHomCongr (V := q) (SSet.comp_const δ v) rfl
          (rightKanHomMap δ α (SSet.const v) ε)) := by
    funext β
    exact rightKanHomMap_constant_comp δ α β ε
  rw [he] at hb
  exact hb.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
