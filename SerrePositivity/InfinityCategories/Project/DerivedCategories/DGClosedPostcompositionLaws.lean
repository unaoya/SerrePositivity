module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionNaturality

/-! # 閉零射の後合成の厳密な関手則と交換則

概要：全 Hom と実 pinched Hom の後合成は dg 関手と前合成に厳密に可換する。
方針：標準豊穣 Hom の自然性と交換則を鎖写像から単体集合へ移す。
規約：全次数、全次元で等式。使われ方：有限族の実 Ore 細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 全 Hom 後合成の dg 関手自然性。 -/
lemma dgClosedPostcomposition_naturality (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := x) s ≫ F.map x z =
      F.map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A E (x := F.obj x) (F.onClosed.map s) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_postcompose F (ForgetEnrichment.of (Complex A) x) s

variable [Small.{u} D] [Small.{u} E]

/-- 全 Hom の前後合成の厳密な交換。 -/
lemma dgClosedPostcomposition_precomposition {q x y z : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := x) s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := z) r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := q) s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_eq_whisker, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition]
  exact eHom_whisker_exchange (_root_.SerrePositivity.DifferentialGraded.Complex A) r s

omit [Small.{u} D] [Small.{u} E] in
/-- 実 pinched Hom の後合成の dg 関手自然性。 -/
lemma pinchedClosedPostcomposition_naturality (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D (x := x) s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x z) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A E (x := F.obj x) (F.onClosed.map s) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp,
    dgClosedPostcomposition_naturality]

/-- 実 pinched Hom の前後合成の厳密な交換。 -/
lemma pinchedClosedPostcomposition_precomposition {q x y z : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D (x := x) s ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := z) r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) r ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D (x := q) s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, dgClosedPostcomposition_precomposition]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
