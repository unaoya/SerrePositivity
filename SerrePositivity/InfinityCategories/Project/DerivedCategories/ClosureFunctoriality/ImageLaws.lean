module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FullFunctor
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomConjugation

/-!
概要：指定実比較データの恒等・合成と、全 Hom 共役の厳密な合成式。
方針：比較同型を関手で写して連結し、中間の共役を相殺する。
規約：独立に再選択した代表の一致を仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 恒等関手には恒等対象写像と恒等実比較を使う。 -/
def DGModuleStrictImage.id (S : Set (ModuleCategory R C)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C C (DGFunctor.id _) S S where
  obj M := M
  iso _ := Iso.refl _

/-- 恒等比較の共役関手は、元の部分 dg 圏の恒等関手。 -/
lemma DGModuleStrictImage.id_functor (S : Set (ModuleCategory R C)) :
    ((DGModuleStrictImage.id R C S).functor R C C (DGFunctor.id _) S S) =
      DGFunctor.id {M // S M} := by
  refine EnrichedFunctor.ext (Complex R) ?_ ?_
  · intro M; rfl
  intro M N
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.functor_map]
  simp only [DGModuleStrictImage.id, DGFunctor.id, EnrichedFunctor.id,
    Category.comp_id, eqToHom_refl]
  change 𝟙 _ ≫ enrichedClosedIsoConjugation (Complex R)
    (Iso.refl M.val) (Iso.refl N.val) = 𝟙 _
  rw [enrichedClosedIsoConjugation_refl, Category.id_comp]

variable (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (RightModule R C) (RightModule R D))
  (G : DGFunctor R (RightModule R D) (RightModule R E))
  (S : Set (ModuleCategory R C)) (T : Set (ModuleCategory R D))
  (U : Set (ModuleCategory R E))
  (I : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D F S T) (J : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R D E G T U)

/-- 指定比較を写して連結する合成。新しい代表選択を行わない。 -/
def DGModuleStrictImage.comp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C E (F.comp G) S U where
  obj M := J.obj (I.obj M)
  iso M := G.onClosed.mapIso (I.iso M) ≪≫ J.iso (I.obj M)

/-- 逐次の全 Hom 共役は、合成された指定比較による一回の共役と等しい。 -/
lemma DGModuleStrictImage.comp_map (M N : {M // S M}) :
    (I.functor R C D F S T).map M N ≫
      (J.functor R D E G T U).map (I.obj M) (I.obj N) =
    ((I.comp R C D E F G S T U J).functor R C E (F.comp G) S U).map M N := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.functor_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.functor_map,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.functor_map]
  simp only [DGModuleStrictImage.comp, DGFunctor.comp, EnrichedFunctor.comp]
  rw [Category.assoc, ← Category.assoc (enrichedClosedIsoConjugation _ _ _),
    dgFunctorHom_conjugation R G, Category.assoc, Category.assoc,
    enrichedClosedIsoConjugation_trans]
  rfl

/-- 保持した比較データの合成は、部分 dg 圏間の関手の合成と厳密一致する。 -/
lemma DGModuleStrictImage.comp_functor :
    ((I.comp R C D E F G S T U J).functor R C E (F.comp G) S U) =
      (I.functor R C D F S T).comp (J.functor R D E G T U) := by
  refine EnrichedFunctor.ext (Complex R) ?_ ?_
  · intro M; rfl
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  exact (I.comp_map R C D E F G S T U J M N).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
