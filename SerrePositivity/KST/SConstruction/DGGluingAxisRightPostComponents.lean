module
public import SerrePositivity.KST.SConstruction.DGGluingAxesArrows
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Postcomposition

/-! # 元の右軸包含の全 Hom 後合成の二成分
概要：右軸包含による後合成は、左 Hom 成分を零にし、元の右 Hom 成分を保持する。
方針：元の両射影の後合成自然性と、閉零左対象への全 Hom の零性を使う。
規約：同じ元の包含射。使われ方：標準 cocone 包含との成分照合。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma postIdentity {V : Type*} [Category V] [MonoidalCategory V]
    {E : Type*} [Category E] [EnrichedOrdinaryCategory V E]
    (A B : E) {K : V} (k : K ⟶ (A ⟶[V] B)) (a : B ⟶ B) (ha : a = 𝟙 B) :
    k ≫ eHomWhiskerLeft V A a = k := by
  rw [ha, eHomWhiskerLeft_id, Category.comp_id]
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 同じ右軸包含の全 Hom 後合成の左成分は厳密に零。 -/
lemma dgGluingAxisRightInclusion_post_left :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T (dgGluingRightAxisObject R C D M z X.right) X
      (dgGluingAxisRightInclusion R C D M z hz X) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M T X = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_left R C D M T
    (dgGluingRightAxisObject R C D M z X.right) X
    (dgGluingAxisRightInclusion R C D M z hz X)
  exact h.trans ((congrArg (fun k => k ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) T.left)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onClosed.map
        (dgGluingAxisRightInclusion R C D M z hz X)))
    ((dgHom_isZero_of_closed_zero_target R z hz T.left).eq_zero_of_tgt
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M T (dgGluingRightAxisObject R C D M z X.right)))).trans
        (zero_comp))

/-- 同じ右軸包含の全 Hom 後合成の右成分は、元の右 Hom 射影を保持する。 -/
lemma dgGluingAxisRightInclusion_post_right :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T (dgGluingRightAxisObject R C D M z X.right) X
      (dgGluingAxisRightInclusion R C D M z hz X) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T X =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M T (dgGluingRightAxisObject R C D M z X.right) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_right R C D M T
    (dgGluingRightAxisObject R C D M z X.right) X
    (dgGluingAxisRightInclusion R C D M z hz X)).trans
      (postIdentity (ForgetEnrichment.of (Complex R) T.right)
        (ForgetEnrichment.of (Complex R) X.right) _ _
        (dgGluingAxisRightInclusion_right R C D M z hz X))

end SerrePositivity.KST.SConstruction
