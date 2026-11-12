module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionTransport
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：元の指定切断から作った Hom span の単位比較は、射影後に同じ切断等式へ戻る。
方針：充満忠実な後合成による同型の逆像の回収則を使う。
規約：既存の指定切断と単位同型を保持する。
使われ方：大域自然性と局所輸送の共有頂点での三角形の等式。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 恒等同型の両端を等号で移したものは、その両端の等号による同型。 -/
lemma iso_refl_cast_eqToIso {C : Type u} [Category.{v} C] {x y z : C}
    (hx : x = z) (hy : y = z) (h : (x ≅ y) = (z ≅ z)) :
    h.mpr (Iso.refl z) = eqToIso (hx.trans hy.symm) := by
  subst x
  subst y
  rfl

/-- 同じ指定切断の単位同型は、元の射影に沿って同じ等号の同型へ戻る。 -/
lemma homSpanSectionSourceIso_projection
    {P X : SSet.{u}} [Quasicategory P] [Quasicategory X]
    (p : P ⟶ X) (s : X ⟶ P) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (hs : s ≫ p = 𝟙 X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionSourceIso p s hp hs).postcomp p =
      eqToIso (congrArg (fun v : P ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v))
        (show (p ≫ s) ≫ p = 𝟙 P ≫ p by
          simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionSourceIso
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence.IsFullyFaithful.preimageFunctorIso_postcomp]
  exact iso_refl_cast_eqToIso
    (congrArg (fun v : P ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v))
      (show (p ≫ s) ≫ p = p by rw [Category.assoc, hs, Category.comp_id]))
    (congrArg (fun v : P ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v))
      (Category.id_comp p)) _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
