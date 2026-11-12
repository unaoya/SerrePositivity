module
public import SerrePositivity.KST.SConstruction.DGClosedComparisonReflection
public import SerrePositivity.KST.SConstruction.DGGluingAxesArrows
public import SerrePositivity.KST.SConstruction.DGGluingAxesMixedHom

/-! # 元の二軸への二射の全 Hom 自然性
概要：同じ右軸からの射と左軸への射は、元の全 Hom 複体の作用と厳密に可換である。
方針：混合 Hom の元の射影同型で反映し、射影後は恒等成分と厳密切断で判定する。
規約：閉零射だけへ弱めない。使われ方：元の短複体の関手性と cofiber 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma identityComparison {V : Type*} [Category V] [MonoidalCategory V]
    {B : Type*} [Category B] [EnrichedOrdinaryCategory V B]
    {K : V} (X Y : B) (k l : K ⟶ (X ⟶[V] Y)) (a : X ⟶ X) (b : Y ⟶ Y)
    (ha : a = 𝟙 X) (hb : b = 𝟙 Y) (hk : k = l) :
    k ≫ eHomWhiskerLeft V X b = l ≫ eHomWhiskerRight V a Y := by
  subst a
  subst b
  rw [eHomWhiskerLeft_id, eHomWhiskerRight_id, hk]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の実右軸からの同じ射は、元の全 Hom 作用について自然。 -/
lemma dgGluingAxisRightInclusion_hom_naturality (z : C)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M z hz)).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgGluingRightAxisObject R C D M z X.right))
        (dgGluingAxisRightInclusion R C D M z hz Y) =
    (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).map X Y ≫
      eHomWhiskerRight (Complex R) (dgGluingAxisRightInclusion R C D M z hz X)
        (ForgetEnrichment.of (Complex R) Y) := by
  apply dgClosedComparison_reflect (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)
    (ForgetEnrichment.of (Complex R) (dgGluingRightAxisObject R C D M z X.right))
    (ForgetEnrichment.of (Complex R) (dgGluingRightAxisObject R C D M z Y.right))
    (ForgetEnrichment.of (Complex R) X) (ForgetEnrichment.of (Complex R) Y)
    _ _ _ _ (dgGluingFromRightAxisHomIso R C D M z hz X.right Y)
    ((dgGluingFromRightAxisHomIso_hom R C D M z hz X.right Y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map R C D M _ _).symm)
  have hs : (dgGluingRightAxis R C D M z hz).map X.right Y.right ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).map
        (dgGluingRightAxisObject R C D M z X.right)
        (dgGluingRightAxisObject R C D M z Y.right) = 𝟙 _ :=
    (congrArg (fun k => (dgGluingRightAxis R C D M z hz).map X.right Y.right ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map R C D M _ _)).trans
        (dgGluingRightAxis_map_right R C D M z hz X.right Y.right)
  exact identityComparison
    (ForgetEnrichment.of (Complex R) X.right) (ForgetEnrichment.of (Complex R) Y.right)
    _ _ _ _ (dgGluingAxisRightInclusion_right R C D M z hz X)
    (dgGluingAxisRightInclusion_right R C D M z hz Y)
    ((((Category.assoc _ _ _).trans
      (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).map X Y ≫ k) hs)).trans
        (Category.comp_id _)).trans (Category.id_comp _).symm)

/-- 元の実左軸への同じ射も、元の全 Hom 作用について自然。 -/
lemma dgGluingAxisLeftProjection_hom_naturality (z : D)
    (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (DGFunctor.id (A := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).map X Y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X)
        (dgGluingAxisLeftProjection R C D M z hz Y) =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).comp (dgGluingLeftAxis R C D M z hz)).map X Y ≫
      eHomWhiskerRight (Complex R) (dgGluingAxisLeftProjection R C D M z hz X)
        (ForgetEnrichment.of (Complex R) (dgGluingLeftAxisObject R C D M z Y.left)) := by
  apply dgClosedComparison_reflect (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)
    (ForgetEnrichment.of (Complex R) X) (ForgetEnrichment.of (Complex R) Y)
    (ForgetEnrichment.of (Complex R) (dgGluingLeftAxisObject R C D M z X.left))
    (ForgetEnrichment.of (Complex R) (dgGluingLeftAxisObject R C D M z Y.left))
    _ _ _ _ (dgGluingToLeftAxisHomIso R C D M z hz X Y.left)
    (dgGluingToLeftAxisHomIso_hom R C D M z hz X Y.left)
  exact identityComparison
    (ForgetEnrichment.of (Complex R) X.left) (ForgetEnrichment.of (Complex R) Y.left)
    _ _ _ _ (dgGluingAxisLeftProjection_left R C D M z hz X)
    (dgGluingAxisLeftProjection_left R C D M z hz Y)
    ((Category.id_comp _).trans
      (((Category.assoc _ _ _).trans
        (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).map X Y ≫ k)
          (dgGluingLeftAxis_map_left R C D M z hz X.left Y.left))).trans
            (Category.comp_id _)).symm)

end SerrePositivity.KST.SConstruction
