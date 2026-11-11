module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeEndSquare
public import SerrePositivity.KST.SConstruction.DGFunctorNativeEvaluationPoint

/-!
概要：元全 end cone 四角形の点評価を、元 dg 加群 cone 四角形へ厳密に回収する。
方針：元両二単体の三辺と次数 −1 成分を同時に照合して貼合せへ戻す。
規約：元の実 cone・指定零化元・元零角を変更しない。
使われ方：全 cone 図式の対象別押し出し性と元逆回転の比較。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open scoped Simplicial
noncomputable section
namespace SerrePositivity.KST.SConstruction
universe u
/-- 概要：元全 end 下二単体の点評価は元実 cone の指定零化面そのもの。
方針：元三辺と同じ左包含原始元を全て回収する。
規約：全二単体の厳密等号。使われ方：元 cone 全四角形の点評価。 -/
lemma dgModuleNaturalConeEndTriangle_evaluation (R : Type u) [CommRing R] (D P : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
    (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x : P) :
    (dgModuleNaturalConeEndTriangle R D F G η).map
      (dgFunctorEvaluationDG R P (RightModule R D) x) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle R D (dgModuleNaturalConeArrow R D F G η x)).simplex := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleEquiv).injective
  change ((dgModuleNaturalConeEndTriangle R D F G η).map
      (dgFunctorEvaluationDG R P (RightModule R D) x)).toTriangle =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLowerTriangle R D (dgModuleNaturalConeArrow R D F G η x)).simplex.toTriangle
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toTriangle
  congr 1
  · funext i
    fin_cases i <;> rfl
  · apply Subtype.ext
    change (dgFunctorHomπ R P (RightModule R D) F G x).f 0
      (dgStrictNatTransEndElement R P (RightModule R D) η) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R D F G η x))).val
    exact (dgStrictNatTransEndElement_π R P (RightModule R D) η x).trans
      (dgModuleNaturalConeArrow_cycle R D F G η x).symm
  · apply Subtype.ext
    change (dgFunctorHomπ R P (RightModule R D) G (dgModuleNaturalConeFunctor R D F G η) x).f 0
      (dgStrictNatTransEndElement R P (RightModule R D) (dgModuleNaturalConeInr R D F G η)) = _
    exact dgStrictNatTransEndElement_π R P (RightModule R D) (dgModuleNaturalConeInr R D F G η) x
  · apply Subtype.ext
    change (dgFunctorHomπ R P (RightModule R D) F (dgModuleNaturalConeFunctor R D F G η) x).f 0
      (0 : (dgFunctorHom R P (RightModule R D) F (dgModuleNaturalConeFunctor R D F G η)).X 0) = 0
    exact map_zero _
  · change (dgFunctorHomπ R P (RightModule R D) F (dgModuleNaturalConeFunctor R D F G η) x).f (-1)
      (dgModuleNaturalConeEndNullHomotopy R D F G η) = _
    exact dgModuleNaturalConeEndNullHomotopy_π R D F G η x
  · exact proof_irrel_heq _ _

/-- 概要：元全 end 上二単体の点評価は元実零加群を経由する同じ零面。
方針：元三零辺と零原始元を回収する。
規約：全二単体の厳密等号。使われ方：元全 cone 四角形の点評価。 -/
lemma dgModuleNaturalConeEndZeroTriangle_evaluation (R : Type u) [CommRing R]
    (D P : Type (u + 1)) [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
    (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x : P) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndZeroTriangleData R D F G η)).map
      (dgFunctorEvaluationDG R P (RightModule R D) x) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle R D (dgModuleNaturalConeArrow R D F G η x)).simplex := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleEquiv).injective
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndZeroTriangleData R D F G η)).map
      (dgFunctorEvaluationDG R P (RightModule R D) x)).toTriangle =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeUpperTriangle R D (dgModuleNaturalConeArrow R D F G η x)).simplex.toTriangle
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toTriangle
  congr 1
  · funext i
    fin_cases i <;> rfl
  · apply Subtype.ext
    change (dgFunctorHomπ R P (RightModule R D) F
      (dgModuleNaturalConeEndZero R D (P := P)) x).f 0 0 = 0
    exact map_zero _
  · apply Subtype.ext
    change (dgFunctorHomπ R P (RightModule R D)
      (dgModuleNaturalConeEndZero R D (P := P))
      (dgModuleNaturalConeFunctor R D F G η) x).f 0 0 = 0
    exact map_zero _
  · apply Subtype.ext
    change (dgFunctorHomπ R P (RightModule R D) F
      (dgModuleNaturalConeFunctor R D F G η) x).f 0 0 = 0
    exact map_zero _
  · change (dgFunctorHomπ R P (RightModule R D) F
      (dgModuleNaturalConeFunctor R D F G η) x).f (-1) 0 = 0
    exact map_zero _
  · exact proof_irrel_heq _ _

/-- 概要：同じ全 end cone 四角形の点評価は元 dg 加群の実 cone 四角形。
方針：指定上下二単体の厳密回収を正方形の pushout で貼る。
規約：四辺と両二胞体を同時に保持。使われ方：元全族の押し出し性。 -/
lemma dgModuleNaturalConeEndSquare_evaluation (R : Type u) [CommRing R]
    (D P : Type (u + 1)) [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
    (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x : P) :
    dgModuleNaturalConeEndSquare R D F G η ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorEvaluationDG R P (RightModule R D) x) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare R D (dgModuleNaturalConeArrow R D F G η x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← Category.assoc, dgModuleNaturalConeEndSquare_upper,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_upper]
    have ht := SSet.yonedaEquiv_symm_comp
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D)))
      (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (n := SimplexCategory.mk 2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofTriangle (dgModuleNaturalConeEndZeroTriangleData R D F G η))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorEvaluationDG R P (RightModule R D) x))
    exact ht.trans (congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋2⦌ =>
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
        (n := SimplexCategory.mk 2)).symm s)
      (dgModuleNaturalConeEndZeroTriangle_evaluation R D P F G η x))
  · rw [← Category.assoc, dgModuleNaturalConeEndSquare_lower,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_lower]
    have ht := SSet.yonedaEquiv_symm_comp
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D)))
      (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (n := SimplexCategory.mk 2)
      (dgModuleNaturalConeEndTriangle R D F G η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorEvaluationDG R P (RightModule R D) x))
    exact ht.trans (congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋2⦌ =>
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
        (n := SimplexCategory.mk 2)).symm s)
      (dgModuleNaturalConeEndTriangle_evaluation R D P F G η x))

end SerrePositivity.KST.SConstruction
