module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleNerveCoherenceImages
public import SerrePositivity.InfinityCategories.Derived.DGKernelCoherencePathTools
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
private def composeIso {R : Type u} [CommRing R] {B C E : Type*}
    [DGCategory R B] [DGCategory R C] [DGCategory R E] [Small.{u} B] [Small.{u} C]
    {P P' : BimoduleCategory R B C} {Q Q' : BimoduleCategory R C E}
    (e : P ≅ P') (f : Q ≅ Q') :=
  (BimoduleTensor.composeFunctor R B C E).mapIso (Iso.prod e f)

variable (R : Type u) [CommRing R] (B C E F : Type v) (G : Type (max (u + 1) v))
  [DGCategory R B] [DGCategory R C] [DGCategory R E] [DGCategory R F] [DGCategory R G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
/-- 同じ双加群五角の反転経路を、全関手射の等式へ送る。 -/
lemma dgBimoduleNerve_inverse_pentagon_hom
    (P : Bimodule R B C) (Q : Bimodule R C E) (T : Bimodule R E F) (U : Bimodule R F G) :
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.composeMap R B C G (𝟙 (BimoduleCategory.of R B C P))
        (BimoduleTensor.associatorIso R C E F G Q T U).inv) ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B C F G P (BimoduleTensor.compose R C E F Q T) U).inv =
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B C E G P Q (BimoduleTensor.compose R E F G T U)).inv ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B E F G (BimoduleTensor.compose R B C E P Q) T U).inv ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.composeMap R B F G (BimoduleTensor.associatorIso R B C E F P Q T).hom
        (𝟙 (BimoduleCategory.of R F G U))) := by
  let a := BimoduleTensor.associatorIso R B E F G
    (BimoduleTensor.compose R B C E P Q) T U
  let b := BimoduleTensor.associatorIso R B C E G P Q
    (BimoduleTensor.compose R E F G T U)
  let c := composeIso (BimoduleTensor.associatorIso R B C E F P Q T)
    (Iso.refl (BimoduleCategory.of R F G U))
  let d := BimoduleTensor.associatorIso R B C F G P
    (BimoduleTensor.compose R C E F Q T) U
  let e := composeIso (Iso.refl (BimoduleCategory.of R B C P))
    (BimoduleTensor.associatorIso R C E F G Q T U)
  have h := iso_inversePentagonPath a b c d e (BimoduleTensor.pentagon R B C E F G P Q T U)
  dsimp only [a, b, c, d, e, composeIso] at h
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (dgBimoduleFunctorHomFunctor R B G).map m) h

end SerrePositivity.InfinityCategories
