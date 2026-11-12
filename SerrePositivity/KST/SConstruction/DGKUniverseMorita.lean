module
public import SerrePositivity.KST.SConstruction.DGKPerfectComposition
public import SerrePositivity.KST.SConstruction.DGKUniverseQuasiEquivalence

/-! # 元の実 Morita 射の固定入力宇宙への移送
概要：対象ラベルを持ち上げた元の dg 射にも、同じ主 Perf 延長の同値性を移す。
方針：元の持ち上げを、下げる射・元の射・上げる射の厳密合成へ分解する。
規約：元の Hom 複体を変更しない。使われ方：同じ S 内の ⊙→商の Morita 辺。
-/
@[expose] public section
noncomputable section
universe u v w r s
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

/-- 元の持ち上げは、対象を下げ・元の射を適用し・対象を上げる同じ厳密合成。 -/
lemma dgKUniverseLiftFunctor_factorization :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, r, s} F =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, r} R D).comp
        (F.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, w, s} R E)) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change F.map x.label.down y.label.down = 𝟙 _ ≫ (F.map x.label.down y.label.down ≫ 𝟙 _)
  rw [Category.comp_id, Category.id_comp]

/-- 元の Morita 射を対象宇宙へ持ち上げても、同じ実 Perf 延長が同値。 -/
lemma dgKUniverseLiftFunctor_isMorita
    [(quasiEquivalencePerfectExtension R D E F).IsEquivalence] :
    (quasiEquivalencePerfectExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, r, s} F)).IsEquivalence := by
  letI : (quasiEquivalencePerfectExtension R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R E)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R E)
      (dgKUniverseLiftUp_quasiEquivalence R E)).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E)
      (F.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R E))).IsEquivalence :=
    dgKPerfectExtension_comp_isEquivalence R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) F _
  letI : (quasiEquivalencePerfectExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R D)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R D)
      (dgKUniverseLiftDown_quasiEquivalence R D)).isEquivalence_functor
  rw [dgKUniverseLiftFunctor_factorization R D E F]
  exact dgKPerfectExtension_comp_isEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) _ _

end SerrePositivity.KST.SConstruction
