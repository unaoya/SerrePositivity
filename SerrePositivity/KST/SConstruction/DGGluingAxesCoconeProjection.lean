module
public import SerrePositivity.KST.SConstruction.DGGluingHomCoconeModel
public import SerrePositivity.KST.SConstruction.DGGluingAxesArrows
public import SerrePositivity.KST.SConstruction.MappingCoconeBiprodCofiber
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Postcomposition

/-! # 元の左軸射と二成分 cocone の第一射影
概要：元の左軸射の全 Hom 後合成を、同じ左 Hom 射影に厳密に照合する。
方針：元の dg 左射影の後合成自然性と、左軸 Hom 同型の順射を使う。
規約：同じ対象・閉射・鎖写像を保持。使われ方：実二軸列の cofiber 比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma postIdentity {V : Type*} [Category V] [MonoidalCategory V]
    {E : Type*} [Category E] [EnrichedOrdinaryCategory V E]
    (A B : E) {K : V} (k : K ⟶ (A ⟶[V] B)) (a : B ⟶ B) (ha : a = 𝟙 B) :
    k ≫ eHomWhiskerLeft V A a = k := by
  rw [ha, eHomWhiskerLeft_id, Category.comp_id]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : D) (hz : IsZero (ForgetEnrichment.of (Complex R) z))
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 元の左軸射の後合成は、同じ Hom 同型の下で元の左 Hom 射影そのもの。 -/
lemma dgGluingAxisLeftProjection_postcompose_hom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T X (dgGluingLeftAxisObject R C D M z X.left)
      (dgGluingAxisLeftProjection R C D M z hz X) ≫
      (dgGluingToLeftAxisHomIso R C D M z hz T X.left).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M T X := by
  rw [dgGluingToLeftAxisHomIso_hom]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_left R C D M T X
    (dgGluingLeftAxisObject R C D M z X.left)
    (dgGluingAxisLeftProjection R C D M z hz X)).trans
      (postIdentity (ForgetEnrichment.of (Complex R) T.left)
        (ForgetEnrichment.of (Complex R) X.left) _ _
        (dgGluingAxisLeftProjection_left R C D M z hz X))

/-- 全 Hom の標準 cocone 比較後の第一射影も、元の同じ左 Hom 射影。 -/
lemma dgGluingHomBiprodCoconeIso_projection :
    (dgGluingHomBiprodCoconeIso R C D M T X).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M T X := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ biprod.fst) (dgGluingHomBiprodCoconeIso_fst R C D M T X))

/-- 元の左軸射と標準モデルの第一射影の比較正方形は、厳密に可換。 -/
lemma dgGluingAxesCoconeProjection_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M T X (dgGluingLeftAxisObject R C D M z X.left)
      (dgGluingAxisLeftProjection R C D M z hz X) ≫
      (dgGluingToLeftAxisHomIso R C D M z hz T X.left).hom =
    (dgGluingHomBiprodCoconeIso R C D M T X).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M T X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M T X) :=
  (dgGluingAxisLeftProjection_postcompose_hom R C D M z hz T X).trans
    (dgGluingHomBiprodCoconeIso_projection R C D M T X).symm

end SerrePositivity.KST.SConstruction
