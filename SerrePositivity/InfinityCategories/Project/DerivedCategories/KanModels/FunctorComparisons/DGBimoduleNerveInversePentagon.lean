module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGBimoduleNerveCoherenceImages
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCoherencePathTools
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
/-!
概要：同じ双加群五角の逆向き経路を、実 h Fun 内で照合する。
方針：元の dg 五角を同型として反転してから、同じ実関手で写す。
規約：通常 kernel の指定比較への同定とは区別する。使われ方：kernel の pentagon。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
private def composeIso {R : Type u} [CommRing R] {B C E : Type*}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} B] [Small.{u} C]
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R B C} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C E}
    (e : P ≅ P') (f : Q ≅ Q') :=
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor R B C E).mapIso (Iso.prod e f)

variable (R : Type u) [CommRing R] (B C E F : Type v) (G : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
/-- 同じ双加群五角の反転経路を、全関手射の等式へ送る。 -/
lemma dgBimoduleNerve_inverse_pentagon_hom
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R B C) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R C E) (T : _root_.SerrePositivity.DifferentialGraded.Bimodule R E F) (U : _root_.SerrePositivity.DifferentialGraded.Bimodule R F G) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B C G (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R B C P))
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R C E F G Q T U).inv) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C F G P (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R C E F Q T) U).inv =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E G P Q (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E F G T U)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B E F G (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R B C E P Q) T U).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R B F G (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P Q T).hom
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R F G U))) := by
  let a := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B E F G
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R B C E P Q) T U
  let b := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E G P Q
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E F G T U)
  let c := composeIso (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C E F P Q T)
    (Iso.refl (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R F G U))
  let d := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R B C F G P
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R C E F Q T) U
  let e := composeIso (Iso.refl (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R B C P))
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso R C E F G Q T U)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_inversePentagonPath a b c d e (BimoduleTensor.pentagon R B C E F G P Q T U)
  dsimp only [a, b, c, d, e, composeIso] at h
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R B G).map m) h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
