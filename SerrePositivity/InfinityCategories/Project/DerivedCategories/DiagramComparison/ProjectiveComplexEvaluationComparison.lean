module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProjectiveOutputResolvedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedSemifreeComparison

/-!
概要：射影的な定数一点加群を持つ複体の、通常評価と指定射影的模型の評価を比較する。
方針：元のdg包含の前合成比較と射影的出力の比較を閉nerveへ制限する。
規約：既存の複体と鎖写像を保持する。新たな導来圏の定義は作らない。
使われ方：3b-3 R6、直和実現を頂点とする全関手族の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

/-- 定数一点加群が全Homの意味で射影的である複体の条件。 -/
def projectiveRingComplexProperty (X : Complex A) : Prop :=
  dgModuleProjectiveProperty A PUnit.{1} ((ringConstantDG A).obj X)

/-- 元の全次数Homを保つ、上の条件の複体の充満dg部分圏。 -/
abbrev ProjectiveRingComplex := DGFullSubcategory (Complex A) (projectiveRingComplexProperty A)

/-- 元の複体へのdg包含。 -/
def projectiveRingComplexInclusion : DGFunctor A (ProjectiveRingComplex A) (Complex A) :=
  dgFullSubcategoryInclusion A (Complex A) (projectiveRingComplexProperty A)

/-- 同じ複体を、指定射影的一点加群として読むdg関手。 -/
def projectiveRingComplexConstant :
    DGFunctor A (ProjectiveRingComplex A) (ProjectiveDGModules A PUnit.{1}) where
  obj X := ⟨(ringConstantDG A).obj X.val, X.property⟩
  map X Y := (ringConstantDG A).map X.val Y.val
  map_id X := (ringConstantDG A).map_id X.val
  map_comp X Y Z := (ringConstantDG A).map_comp X.val Y.val Z.val

/-- 複体の包含を通す定数加群は、射影的出力の同じ包含と一致する。 -/
lemma projectiveRingComplexInclusion_constant :
    (projectiveRingComplexInclusion A).comp (ringConstantDG A) =
      (projectiveRingComplexConstant A).comp
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleProjectiveProperty A PUnit.{1})) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro X Y
  simp [projectiveRingComplexInclusion, projectiveRingComplexConstant,
    EnrichedFunctor.comp_map, dgFullSubcategoryInclusion]

/-- 元の同じ射影的複体の上で、実分解と指定射影的模型は全関手同型。 -/
def projectiveRingComplexResolvedIso :
    FunctorIso
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (projectiveRingComplexInclusion A) ≫
          dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
            (semifreePointEquivalence A).hom)
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (projectiveRingComplexConstant A) ≫ (projectivePointEquivalence A).hom) := by
  have e := dgModuleResolvedInfinity_precompIso A (ProjectiveRingComplex A) (Complex A) PUnit.{1}
    (projectiveRingComplexInclusion A) (ringConstantDG A)
  rw [projectiveRingComplexInclusion_constant] at e
  exact (e.postcomp (semifreePointEquivalence A).hom).symm ≪≫
    projectiveOutputResolvedPointIso A (ProjectiveRingComplex A) (projectiveRingComplexConstant A)

/-- 閉零射の射影的複体を、同じ通常鎖写像で読む。 -/
def projectiveRingUnderlyingComplex : ClosedCategory A (ProjectiveRingComplex A) ⥤ Complex A :=
  (projectiveRingComplexInclusion A).onClosed ⋙ closedToComplex A

/-- 閉零射から通常射へ表示を通しても、元の射影的複体の包含は変わらない。 -/
lemma projectiveRingUnderlyingComplex_presentation :
    projectiveRingUnderlyingComplex A ⋙ complexClosedPresentation A =
      (projectiveRingComplexInclusion A).onClosed := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro X
    rfl
  intro X Y f
  change (complexClosedHomEquiv A _ _).symm
    (complexClosedHomEquiv A _ _ ((projectiveRingComplexInclusion A).onClosed.map f)) = _
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    (Equiv.symm_apply_apply (complexClosedHomEquiv A _ _)
      ((projectiveRingComplexInclusion A).onClosed.map f))

/-- 射影的複体の全nerve上の、同じD(A)へ着地する全評価の比較。 -/
def complexDerivedEvaluation_projectiveRingIso :
    FunctorIso
      (nerveMap (projectiveRingUnderlyingComplex A) ≫ complexDerivedEvaluation A)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (projectiveRingComplexConstant A) ≫ (projectivePointEquivalence A).hom) := by
  have e := (projectiveRingComplexResolvedIso A).precomp
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A))
  have he : nerveMap (projectiveRingUnderlyingComplex A) ≫ complexDerivedEvaluation A =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (projectiveRingComplexInclusion A) ≫
            dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
              (semifreePointEquivalence A).hom := by
    have hn : nerveMap (projectiveRingUnderlyingComplex A) ≫ nerveMap (complexClosedPresentation A) =
        nerveMap (projectiveRingComplexInclusion A).onClosed := by
      change nerveMap (projectiveRingUnderlyingComplex A ⋙ complexClosedPresentation A) = _
      rw [projectiveRingUnderlyingComplex_presentation]
    simp only [complexDerivedEvaluation, ← Category.assoc]
    rw [closedNerveInclusion_dgFunctor, hn]
  rw [he]
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
