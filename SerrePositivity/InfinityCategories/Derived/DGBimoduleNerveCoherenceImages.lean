module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.DifferentialGraded.Tensor.Triangle
public import SerrePositivity.DifferentialGraded.Tensor.Pentagon
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B C E F : Type v) (G : Type (max (u + 1) v))
  [DGCategory R B] [DGCategory R C] [DGCategory R E] [DGCategory R F] [DGCategory R G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]
/-- 元の閉零双加群 triangle の全関手射としての実 nerve 像。 -/
lemma dgBimoduleNerve_triangle_hom (P : Bimodule R B C) (Q : Bimodule R C G) :
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.composeMap R B C G (BimoduleTensor.rightBimoduleUnitIso R B C P).hom
        (𝟙 (BimoduleCategory.of R C G Q))) =
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B C C G P (Bimodule.diagonal R C) Q).hom ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.composeMap R B C G (𝟙 (BimoduleCategory.of R B C P))
        (BimoduleTensor.leftBimoduleUnitIso R C G Q).hom) := by
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (dgBimoduleFunctorHomFunctor R B G).map m)
    (BimoduleTensor.triangle R B C G P Q)
/-- 元の閉零双加群 pentagon の全関手射としての実 nerve 像。 -/
lemma dgBimoduleNerve_pentagon_hom
    (P : Bimodule R B C) (Q : Bimodule R C E) (T : Bimodule R E F) (U : Bimodule R F G) :
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B E F G (BimoduleTensor.compose R B C E P Q) T U).hom ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B C E G P Q (BimoduleTensor.compose R E F G T U)).hom =
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.composeMap R B F G (BimoduleTensor.associatorIso R B C E F P Q T).hom
        (𝟙 (BimoduleCategory.of R F G U))) ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.associatorIso R B C F G P (BimoduleTensor.compose R C E F Q T) U).hom ≫
    (dgBimoduleFunctorHomFunctor R B G).map
      (BimoduleTensor.composeMap R B C G (𝟙 (BimoduleCategory.of R B C P))
        (BimoduleTensor.associatorIso R C E F G Q T U).hom) := by
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg
    (fun m => (dgBimoduleFunctorHomFunctor R B G).map m)
    (BimoduleTensor.pentagon R B C E F G P Q T U)
end SerrePositivity.InfinityCategories
