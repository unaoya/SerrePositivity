module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedSquareHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeSquare

/-!
閉じた gluing 射の実第三成分を用いる、cone の比較係数。
左成分の代表加群の cone から右成分の双加群像の cone への実鎖写像を、全対象で構成する。
右成分の cone の表現可能性、全 dg 自然性、前三角性はここでは結論に含めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
  (f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y)

/-- 比較ホモトピーを保持する、元の閉射の全対象での cone 係数。 -/
def dgGluingCommaConeCoefficient (c : C) :
    mappingCone ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f)) ⟶
    mappingCone ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap _ _
    ((moduleEvaluation R C c).map X.augmentation)
    ((moduleEvaluation R C c).map Y.augmentation)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy R C D M X Y f c)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy_equation R C D M X Y f c)

/-- cone の右包含は標的の元の augmentation と厳密に可換。 -/
lemma dgGluingCommaConeCoefficient_inr (c : C) :
    mappingCone.inr ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f)) ≫
      dgGluingCommaConeCoefficient R C D M X Y f c =
    (moduleEvaluation R C c).map Y.augmentation ≫
      mappingCone.inr ((moduleEvaluation R C c).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inr _ _ _ _ _ _

/-- cone の左包含は指定第三成分を含む同じ非対角項を回収する。 -/
lemma dgGluingCommaConeCoefficient_inl (c : C) :
    (mappingCone.inl ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f))).comp
      (Cochain.ofHom (dgGluingCommaConeCoefficient R C D M X Y f c)) (add_zero (-1)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquarePrimitive
      ((moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f))
      ((moduleEvaluation R C c).map X.augmentation)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy R C D M X Y f c) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inl _ _ _ _ _ _

variable (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (g : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)

/-- 元の native gluing の閉射から得る、代表加群表示の実 cone 係数。 -/
abbrev dgGluingConeCoefficient (c : C) :=
  dgGluingCommaConeCoefficient R C D M
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map g) c

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
