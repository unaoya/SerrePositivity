module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeModuleBoundaryElement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.YonedaConeEvaluation

/-! 指定 cochain を保持する、Yoneda 加群円錐から選んだ gluing 対象の代表加群への実閉射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "yf" => CategoryTheory.Functor.map (DGFunctor.onClosed (dgYoneda R G)) f
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInrModuleMap R C D M Y Z f p q

/-- 全 dg 自然な Hom end 内の指定境界元による、同じ Yoneda 加群円錐からの実閉射。 -/
def dgGluingConeModuleMap : moduleCone R G yf ⟶
    ForgetEnrichment.of (Complex R) (representable R W) :=
  moduleConeDescOfBoundary R G yf (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleNullElement R C D M Y Z f p q) b
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleNullElement_boundary R C D M Y Z f p q)

/-- この全 dg 自然な円錐射は、元の同じ Yoneda 加群包含を延長する。 -/
lemma dgGluingConeModuleMap_inr :
    moduleConeInr R G yf ≫ dgGluingConeModuleMap R C D M Y Z f p q = b :=
  moduleConeDescOfBoundary_inr R G yf _ b _

/-- native Hom の円錐と、同じ Yoneda 加群円錐の評価との等式による同型。 -/
def dgGluingConeModuleEvaluationIso (X : G) :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ≅
      (moduleEvaluation R G X).obj (moduleCone R G yf) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeEvaluationIso R G X Y Z f

/-- 評価との比較は、native の同じ右包含を評価された右包含へ送る。 -/
lemma dgGluingConeModuleEvaluationIso_inr (X : G) :
    mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ≫
      (dgGluingConeModuleEvaluationIso R C D M Y Z f X).hom =
    mappingCone.inr ((moduleEvaluation R G X).map yf) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeEvaluationIso_inr R G X Y Z f

/-- 評価との比較は、native の同じ次数 −1 の左包含も保つ。 -/
lemma dgGluingConeModuleEvaluationIso_inl (X : G) :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingConeModuleEvaluationIso R C D M Y Z f X).hom)
      (add_zero (-1)) = mappingCone.inl ((moduleEvaluation R G X).map yf) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeEvaluationIso_inl R G X Y Z f

/-- 加群円錐射の評価を、元の同じ native Hom 円錐を始域に持つ実鎖写像として読む。 -/
def dgGluingConeModuleMapEvaluation (X : G) :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X W :=
  (dgGluingConeModuleEvaluationIso R C D M Y Z f X).hom ≫
    (moduleEvaluation R G X).map (dgGluingConeModuleMap R C D M Y Z f p q)

/-- 各試験対象での右成分も、元の native 円錐包含による後合成そのもの。 -/
lemma dgGluingConeModuleMap_eval_inr (X : G) :
    mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ≫
      dgGluingConeModuleMapEvaluation R C D M Y Z f p q X =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Z W (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr R C D M Y Z f p q) := by
  have he := congrArg ((moduleEvaluation R G X).map)
    (dgGluingConeModuleMap_inr R C D M Y Z f p q)
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInrModuleMap_eval] at he
  rw [dgGluingConeModuleMapEvaluation, ← Category.assoc, dgGluingConeModuleEvaluationIso_inr]
  exact he

omit p q in
/-- 元の両圏の前三角性を明示入力に、同じ円錐対象への全 dg 自然な加群円錐射を供給。 -/
def dgGluingChosenConeModuleMap (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    moduleCone R G yf ⟶
    ForgetEnrichment.of (Complex R)
      (representable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject R C D M Y Z f hC hD)) :=
  dgGluingConeModuleMap R C D M Y Z f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R C Y.left Z.left
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f) hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R D Y.right Z.right
      ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)) hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
