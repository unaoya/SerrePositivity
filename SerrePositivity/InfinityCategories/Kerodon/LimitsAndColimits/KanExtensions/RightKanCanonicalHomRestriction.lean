module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom

/-!
概要：同じ標準右Kan錐で前合成した二胞体を図式側で制限すると、元の添字による前合成となる。
方針：既存の標準形状の全前合成の等式をホモトピー圏へ移し、同じ係数等式の移送を相殺する。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の計算法則。
使われ方：S8 の指定大域比較のhom_facを、元の輸送の基底の辺の類へ渡す。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の全二胞体の標準錐への前合成と図式側の制限は、元の同じ係数移送で可換。 -/
lemma rightKanCanonicalShape_hom_restriction {K C D : SSet.{u}} (δ : K ⟶ C)
    (c : C _⦋0⦌) {U V : C ⟶ D} (α : FunctorHom U V) :
    let j := joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c)
    let q := rightKanCanonicalShape δ c
    let π := rightKanProjection δ c
    let hU : j ≫ (q ≫ U) = π ≫ (δ ≫ U) := by
      rw [← Category.assoc, rightKanCanonicalShape_inr, Category.assoc]
    let hV : j ≫ (q ≫ V) = π ≫ (δ ≫ V) := by
      rw [← Category.assoc, rightKanCanonicalShape_inr, Category.assoc]
    kanFunctorHomCongr hU hV
      ((hoFunctor.map ((pre j).app D)).toFunctor.map
        ((hoFunctor.map ((pre q).app D)).toFunctor.map α)) =
    (hoFunctor.map ((pre π).app D)).toFunctor.map
      ((hoFunctor.map ((pre δ).app D)).toFunctor.map α) := by
  dsimp only
  have hp : (hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c))).app D)).toFunctor =
    (hoFunctor.map ((pre δ).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (rightKanProjection δ c)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Cat.Hom.comp_toFunctor,
      ← Functor.map_comp, ← Functor.map_comp, rightKanCanonicalShape_precomposition]
  have h := Functor.congr_hom hp α
  dsimp only [Functor.comp_map] at h
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
