module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 充満 dg 部分圏への単体的ホモトピーの持ち上げ

概要：両端が充満部分圏に入るホモトピーは全体がその部分圏へ持ち上がる。
方針：円柱の全頂点は両端のいずれかにあり、頂点条件から全写像を持ち上げる。
規約：部分圏や形状に追加の閉性は要求しない。使われ方：D7 の suspension の図式比較を Semifree へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (P : D → Prop)

/-- 両端が充満 dg 部分圏にあるホモトピーは部分圏内へ持ち上がる。 -/
lemma exists_fullInclusion_homotopy {K : SSet.{max u v}}
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.DifferentialGraded.DGFullSubcategory D P))
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R D P))
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R D P))) :
    ∃ L : SSet.Homotopy f g, L.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R D P) = H.h := by
  have hv : ∀ z : (K ⊗ (Δ[1] : SSet.{max u v})) _⦋0⦌, P ((H.h.app _ z).obj 0) := by
    rintro ⟨k, t⟩
    obtain ⟨i, rfl⟩ := (SSet.stdSimplex.obj₀Equiv.symm).surjective t
    fin_cases i
    · have hh := congrArg (fun a => (a.app (Opposite.op ⦋0⦌) k).obj 0) H.h₀
      change (H.h.app _ (k, SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0 =
        ((f.app _ k).obj 0).val at hh
      exact hh.symm ▸ ((f.app _ k).obj 0).property
    · have hh := congrArg (fun a => (a.app (Opposite.op ⦋0⦌) k).obj 0) H.h₁
      change (H.h.app _ (k, SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0 =
        ((g.app _ k).obj 0).val at hh
      exact hh.symm ▸ ((g.app _ k).obj 0).property
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift R D P H.h hv
  have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P) = H.h :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp R D P H.h hv
  refine ⟨{ h := F, h₀ := ?_, h₁ := ?_, rel := ?_ }, hF⟩
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))).1
    rw [Category.assoc, hF]
    exact H.h₀
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))).1
    rw [Category.assoc, hF]
    exact H.h₁
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories
