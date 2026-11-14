module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGConeCoordinateTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGYonedaPostcompositionCone

/-! # Yoneda 後合成 cone 同型の評価と実二座標

概要：実鎖同型で移した cone 元を Yoneda 評価すると、元の二座標が厳密に戻る。
方針：Yoneda の両逆性で等式輸送だけに戻し、その二座標保存を使う。
規約：元の斉次成分を保持。使われ方：残差原始元から細分後の Q・A を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 後合成 cone の実同型と Yoneda 評価の合成は、元の複体等式による輸送。 -/
lemma dgYonedaPostcompositionConeIso_evaluation (x : D) {y z : ClosedCategory A D}
    (g : y ⟶ z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom ≫
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom =
        eqToHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionCone_eq A D x g) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso, Iso.trans_hom, Category.assoc,
    Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, eqToIso.hom]

/-- 同型で移した cone 元の評価の第一座標は、元の第一座標そのもの。 -/
lemma dgYonedaPostcompositionConeIso_fst (x : D) {y z : ClosedCategory A D}
    (g : y ⟶ z) (n : ℤ)
    (a : (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).X n) :
    (mappingCone.fst ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g))).val.v
      n (n + 1) rfl
      ((dgYonedaIso A x (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom.f n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a)) =
      (mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).val.v
        n (n + 1) rfl a := by
  have he := congrArg (fun f => f.f n a) (dgYonedaPostcompositionConeIso_evaluation A D x g)
  have he' :
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom.f n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a) =
      (eqToHom (congrArg (fun f : homObject A D x y ⟶ homObject A D x z => mappingCone f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D x g).symm)).f n a := he
  exact (congrArg ((mappingCone.fst
    ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g))).val.v n (n + 1) rfl)
      he').trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D x g).symm n a)

/-- 同型で移した cone 元の評価の第二座標は、元の第二座標そのもの。 -/
lemma dgYonedaPostcompositionConeIso_snd (x : D) {y z : ClosedCategory A D}
    (g : y ⟶ z) (n : ℤ)
    (a : (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).X n) :
    (mappingCone.snd ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g))).v
      n n (add_zero n)
      ((dgYonedaIso A x (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom.f n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a)) =
      (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).v
        n n (add_zero n) a := by
  have he := congrArg (fun f => f.f n a) (dgYonedaPostcompositionConeIso_evaluation A D x g)
  have he' :
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom.f n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a) =
      (eqToHom (congrArg (fun f : homObject A D x y ⟶ homObject A D x z => mappingCone f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D x g).symm)).f n a := he
  exact (congrArg ((mappingCone.snd
    ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g))).v n n (add_zero n))
      he').trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeEqToHom_snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_postcomposition A D x g).symm n a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
