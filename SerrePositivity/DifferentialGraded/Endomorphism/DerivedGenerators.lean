module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedAdjunction

/-! # 再構成導来随伴による指定対象と正則End加群の比較

正則End加群の射影性で導来tensorを直接計算し、既存のYoneda tensor単位に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 射影的加群について、再構成導来tensorは非導来tensorで計算できる。 -/
def endomorphismDerivedTensorProjectiveComputation
    (N : ModuleCategory A (EndomorphismObject E))
    (hN : moduleHomotopicallyProjective A (EndomorphismObject E) N) :
    (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj N) :=
  endomorphismDerivedTensorResolutionComputation A D E
    { obj := N
      π := 𝟙 N
      projective := hN
      quasiIso := (moduleQuasiIso A (EndomorphismObject E)).id_mem N }

/-- 正則End(E)加群は再構成導来tensorで指定対象Eに送られる。 -/
def endomorphismDerivedTensor_regularIso :
    (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj
          (ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E))))) ≅
      (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E) :=
  endomorphismDerivedTensorProjectiveComputation A D E _
      (representable_homotopicallyProjective A (EndomorphismObject E) .point) ≪≫
    (moduleToDerived A D).mapIso (endomorphismModuleTensor_regularIso A D E)

/-- 指定対象Eの導来Hom像は正則End(E)加群。 -/
def endomorphismDerivedHom_selfIso
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    (endomorphismDerivedHom A D E hE).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) E)) ≅
      (moduleToDerived A (EndomorphismObject E)).obj
        (ForgetEnrichment.of (Complex A) (representable A (EndomorphismObject.point (E := E)))) :=
  endomorphismDerivedHomComputation A D E hE (ForgetEnrichment.of (Complex A) E) ≪≫
    (moduleToDerived A (EndomorphismObject E)).mapIso
      (eqToIso (congrArg (ForgetEnrichment.of (Complex A)) (endomorphismModuleHom_self A D E)))

end SerrePositivity.DifferentialGraded
