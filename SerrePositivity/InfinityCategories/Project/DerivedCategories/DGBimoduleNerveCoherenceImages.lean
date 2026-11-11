module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
/-!
概要：同じ双加群 triangle と pentagon を、実 h Fun の射の等式へ送る。
方針：元の指定値と全 Hom 自然性を保持する実関手を使う。
規約：頂点成分の一致へ弱めない。使われ方：kernel の triangle・pentagon の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (B C E F : Type v) (G : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
/-- 元の閉零双加群 triangle の全関手射としての実 nerve 像。 -/
lemma dgBimoduleNerve_triangle_hom (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R B C) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R C G) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C G (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R B C P).hom
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R C G Q))) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C C G P (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R C) Q).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C G (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R B C P))
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R C G Q).hom) := by
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map m)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.triangle R B C G P Q)
/-- 元の閉零双加群 pentagon の全関手射としての実 nerve 像。 -/
lemma dgBimoduleNerve_pentagon_hom
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R B C) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R C E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E F) (U : _root_.SerrePositivity.DifferentialGraded.Bimodule R F G) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B E F G (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R B C E P Q) T U).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E G P Q (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E F G T U)).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B F G (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P Q T).hom
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R F G U))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C F G P (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R C E F Q T) U).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C G (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R B C P))
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R C E F G Q T U).hom) := by
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map m)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.pentagon R B C E F G P Q T U)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
