module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereFreeLabelAction
/-!
概要：κ 未満自由表示のラベルを保持した小さい dg 圏を構成する。
方針：実 sphere-free 加群の全 Hom 複体を引き戻し、評価を恒等 Hom 作用で与える。
規約：自由基底の試作であり、前三角性や全 κ-compact 被覆はまだ結論しない。
使われ方：ラベルを値域で選び直さない提示模型の基底と Hom 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

/-- 評価後も消去しない κ 未満自由表示のラベル。 -/
structure DGKappaPresentedFreeObject (D : Type v) [Small.{u} D] (κ : Cardinal.{u}) where
  label : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable (κ : Cardinal.{u})

lemma dgKappaPresentedFreeObject_small : Small.{u} (DGKappaPresentedFreeObject D κ) :=
  inferInstance

/-- ラベルの評価は元の同じ実 sphere-free 加群。 -/
def dgKappaPresentedFreeValue (X : DGKappaPresentedFreeObject D κ) : RightModule R D :=
  ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D X.label)

instance dgKappaPresentedFreeEnrichment : DGCategory R (DGKappaPresentedFreeObject D κ) :=
  ofHomObjects R _ (fun X Y => homObject R (RightModule R D)
      (dgKappaPresentedFreeValue R D κ X) (dgKappaPresentedFreeValue R D κ Y))
    (fun X => eId (Complex R) (dgKappaPresentedFreeValue R D κ X))
    (fun X Y Z => eComp (Complex R) (dgKappaPresentedFreeValue R D κ X)
      (dgKappaPresentedFreeValue R D κ Y) (dgKappaPresentedFreeValue R D κ Z))
    (fun X Y => EnrichedCategory.id_comp
      (dgKappaPresentedFreeValue R D κ X) (dgKappaPresentedFreeValue R D κ Y))
    (fun X Y => EnrichedCategory.comp_id
      (dgKappaPresentedFreeValue R D κ X) (dgKappaPresentedFreeValue R D κ Y))
    (fun W X Y Z => EnrichedCategory.assoc (dgKappaPresentedFreeValue R D κ W)
      (dgKappaPresentedFreeValue R D κ X) (dgKappaPresentedFreeValue R D κ Y)
      (dgKappaPresentedFreeValue R D κ Z))

/-- 全次数 Hom 複体を保持する実加群への dg 評価。 -/
def dgKappaPresentedFreeEvaluation :
    DGFunctor R (DGKappaPresentedFreeObject D κ) (RightModule R D) where
  obj := dgKappaPresentedFreeValue R D κ
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

lemma dgKappaPresentedFreeEvaluation_homIso (X Y : DGKappaPresentedFreeObject D κ) :
    IsIso ((dgKappaPresentedFreeEvaluation R D κ).map X Y) := by
  change IsIso (𝟙 _)
  infer_instance

lemma dgKappaPresentedFreeValue_projective (X : DGKappaPresentedFreeObject D κ) :
    moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (dgKappaPresentedFreeValue R D κ X)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_projective R D X.label

end SerrePositivity.InfinityCategories.Project.DerivedCategories
