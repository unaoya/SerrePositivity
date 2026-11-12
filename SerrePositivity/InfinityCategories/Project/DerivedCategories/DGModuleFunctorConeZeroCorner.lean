module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorConeSquareModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareTopMiddleIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareVertices

/-! # cone の押し出し模型の零角を実関手像へ替える

概要：標準零加群の角を F(0) に替えた四角形データは元の標準四角形の実関手像と等しい。
方針：実零加群同型と、cone 同型の二包含の厳密一致を使う。
規約：四辺・対角・二つの Hom end 成分を全て照合。使われ方：標準 cofiber 保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E))
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 零角の実同型と零射は模型の上辺を因子分解する。 -/
lemma dgModuleFunctorConeSquareModel_zero_factorization (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorZeroIso A D E F).hom ≫
      (0 : F.onClosed.obj (_root_.SerrePositivity.DifferentialGraded.moduleZero A D) ⟶ F.onClosed.obj (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareModel A D E F f).top := by
  change _ = 0 ≫ _
  rw [comp_zero, zero_comp]

/-- 実関手像の零加群を左上の角とする模型。 -/
def dgModuleFunctorConeSquareZeroModel (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A E (F.onClosed.obj M) (F.onClosed.obj N)
      (F.onClosed.obj (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) (F.onClosed.obj (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareModel A D E F f).changeTopMiddle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorZeroIso A D E F).hom 0
    (dgModuleFunctorConeSquareModel_zero_factorization A D E F f)

/-- 零角を替えた模型は全データにおいて元の実四角形の関手像と一致する。 -/
lemma dgModuleFunctorConeSquareZeroModel_eq_map (f : M ⟶ N) :
    dgModuleFunctorConeSquareZeroModel A D E F f = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A D f).map F := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.ext
  · rfl
  · change 0 ≫ _ = F.onClosed.map (0 : M ⟶ _root_.SerrePositivity.DifferentialGraded.moduleZero A D)
    rw [zero_comp, Functor.map_zero]
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison_inr A D E F f
  · change 0 = F.onClosed.map (0 : _root_.SerrePositivity.DifferentialGraded.moduleZero A D ⟶ _root_.SerrePositivity.DifferentialGraded.moduleCone A D f)
    rw [Functor.map_zero]
  · change 0 ≫ _ = F.onClosed.map (0 : M ⟶ _root_.SerrePositivity.DifferentialGraded.moduleCone A D f)
    rw [zero_comp, Functor.map_zero]
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison_inl A D E F f
  · change _root_.SerrePositivity.DifferentialGraded.compose A _ 0 (add_zero (-1)) = (F.map _ _).f (-1) 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, map_zero]

/-- 零角を実関手像へ変更する四角形全体の関手同型。 -/
def dgModuleFunctorConeSquareZeroFunctorIso (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareModel A D E F f).square
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A D f).map F).square := by
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareModel A D E F f).square 0 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.square_vertex01]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A E
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgModuleFunctorConeSquareZeroModel A D E F f).square 0 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.square_vertex01]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_of_closed_isZero _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctor_zero_isZero A D E F)
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareModel A D E F f).changeTopMiddleFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorZeroIso A D E F).hom 0
    (dgModuleFunctorConeSquareModel_zero_factorization A D E F f) hs ht
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso _ (dgModuleFunctorConeSquareZeroModel A D E F f).square at h
  rw [dgModuleFunctorConeSquareZeroModel_eq_map] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
