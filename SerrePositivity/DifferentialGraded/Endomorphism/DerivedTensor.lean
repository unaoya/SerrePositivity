module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHom
public import SerrePositivity.DifferentialGraded.Derived.ResolutionFunctorChoice
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveComparison

/-! # 指定dg加群Eとの再構成tensorの導来化

右End(E)加群を射影解像し、主Kを通じてD(D)へ送る。
Eの成分のA-flat性や全加群dg圏の対象型のsmall性は仮定しない。
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

/-- 任意の右End(E)射影解像度族で構成する再構成導来tensor。 -/
def endomorphismResolutionDerivedTensor
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    DerivedModuleCategory A (EndomorphismObject E) ⥤ DerivedModuleCategory A D :=
  moduleDerivedResolutionFunctor A (EndomorphismObject E) R ⋙
    (endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D

/-- 主semifree射影解像度から作る再構成導来tensor。 -/
def endomorphismDerivedTensor :
    DerivedModuleCategory A (EndomorphismObject E) ⥤ DerivedModuleCategory A D :=
  endomorphismResolutionDerivedTensor A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E))

/-- 実際のdg tensor関手とH⁰関手の対象比較。 -/
def endomorphismTensorHomotopyComputation (N : ModuleCategory A (EndomorphismObject E)) :
    (endomorphismModuleTensor A D E).onHomotopy.obj
      ((moduleToHomotopy A (EndomorphismObject E)).obj N) ≅
    (moduleToHomotopy A D).obj ((endomorphismModuleTensor A D E).onClosed.obj N) :=
  eqToIso (congrArg (fun F => F.obj N) (endomorphismModuleTensor A D E).onHomotopy_fac)

/-- 指定局所化の対象での、選んだ射影解像度による実際の計算同型。 -/
def endomorphismResolutionDerivedTensorComputation
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N)
    (N : ModuleCategory A (EndomorphismObject E)) :
    (endomorphismResolutionDerivedTensor A D E R).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj (R N).obj) :=
  ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).mapIso
      (moduleDerivedResolutionComputation A (EndomorphismObject E) R N) ≪≫
    (moduleHomotopyToDerivedClosed A D).mapIso
      (endomorphismTensorHomotopyComputation A D E (R N).obj) ≪≫
    (moduleToHomotopyDerivedIso A D).app ((endomorphismModuleTensor A D E).onClosed.obj (R N).obj)

/-- 任意の二つの射影解像度族を用いた導来tensorの自然な比較。 -/
def endomorphismResolutionDerivedTensorIso
    (R S : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismResolutionDerivedTensor A D E R ≅ endomorphismResolutionDerivedTensor A D E S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A (EndomorphismObject E) R S)
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D)

lemma endomorphismResolutionDerivedTensorIso_self
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismResolutionDerivedTensorIso A D E R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map
    ((moduleDerivedResolutionIso A (EndomorphismObject E) R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map_id _

lemma endomorphismResolutionDerivedTensorIso_trans
    (R S T : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismResolutionDerivedTensorIso A D E R S ≪≫
      endomorphismResolutionDerivedTensorIso A D E S T =
        endomorphismResolutionDerivedTensorIso A D E R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map
      ((moduleDerivedResolutionIso A (EndomorphismObject E) R S).hom.app X) ≫
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map
      ((moduleDerivedResolutionIso A (EndomorphismObject E) S T).hom.app X) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f =>
    ((endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D).map f)
    (NatTrans.congr_app (congrArg Iso.hom
      (moduleDerivedResolutionIso_trans A (EndomorphismObject E) R S T)) X)

/-- 射影的右加群間の擬同型をtensorすると擬同型。Eの成分のflat性は不要。 -/
lemma endomorphismModuleTensor_projective_quasiIso
    {N N' : ModuleCategory A (EndomorphismObject E)}
    (hN : moduleHomotopicallyProjective A (EndomorphismObject E) N)
    (hN' : moduleHomotopicallyProjective A (EndomorphismObject E) N')
    (f : N ⟶ N') (hf : moduleQuasiIso A (EndomorphismObject E) f) :
    moduleQuasiIso A D ((endomorphismModuleTensor A D E).onClosed.map f) := by
  intro d
  rw [endomorphismModuleTensor_map_eval]
  exact BalancedTensor.rightTensor_projective_quasiIso A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) hN hN' f hf

/-- 同じK射を表す閉零射は再構成tensor後の主導来圏でも同じ射となる。 -/
lemma endomorphismTensorDerived_map_eq_of_homotopy_map_eq
    {N N' : ModuleCategory A (EndomorphismObject E)} {f g : N ⟶ N'}
    (h : (moduleToHomotopy A (EndomorphismObject E)).map f =
      (moduleToHomotopy A (EndomorphismObject E)).map g) :
    (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map f) =
      (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map g) :=
  moduleQuasiIso_equalizes_boundary A D (moduleToDerived A D) (moduleToDerived_inverts A D) _ _
    ((endomorphismModuleTensor A D E).preserves_boundary f g
      ((toHomotopy_map_eq_iff A (RightModule A (EndomorphismObject E)) f g).mp h))

/-- 二つの任意射影解像度による実際のtensor計算の同型。 -/
def endomorphismProjectiveResolutionTensorIso
    {N : ModuleCategory A (EndomorphismObject E)}
    (P Q : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P.obj) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj Q.obj) := by
  letI := moduleToDerived_inverts A D _
    (endomorphismModuleTensor_projective_quasiIso A D E P.projective Q.projective
      (P.comparison Q) (P.comparison_quasiIso Q))
  exact asIso ((moduleToDerived A D).map
    ((endomorphismModuleTensor A D E).onClosed.map (P.comparison Q)))

lemma endomorphismProjectiveResolutionTensorIso_hom
    {N : ModuleCategory A (EndomorphismObject E)}
    (P Q : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    (endomorphismProjectiveResolutionTensorIso A D E P Q).hom =
      (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map (P.comparison Q)) :=
  rfl

lemma endomorphismProjectiveResolutionTensorIso_self
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismProjectiveResolutionTensorIso A D E P P = Iso.refl _ := by
  apply Iso.ext
  change (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map
    (P.comparison P)) = 𝟙 _
  have h := endomorphismTensorDerived_map_eq_of_homotopy_map_eq A D E
    (P.comparison_self.trans ((moduleToHomotopy A (EndomorphismObject E)).map_id P.obj).symm)
  simpa only [CategoryTheory.Functor.map_id] using h

lemma endomorphismProjectiveResolutionTensorIso_trans
    {N : ModuleCategory A (EndomorphismObject E)}
    (P Q R : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    endomorphismProjectiveResolutionTensorIso A D E P Q ≪≫
      endomorphismProjectiveResolutionTensorIso A D E Q R =
        endomorphismProjectiveResolutionTensorIso A D E P R := by
  apply Iso.ext
  change (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map
      (P.comparison Q)) ≫
    (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map (Q.comparison R)) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact endomorphismTensorDerived_map_eq_of_homotopy_map_eq A D E
    (((moduleToHomotopy A (EndomorphismObject E)).map_comp (P.comparison Q) (Q.comparison R)).trans
      (P.comparison_comp Q R))

/-- 標準の導来tensorは任意の右End(E)射影解像度で計算できる。 -/
def endomorphismDerivedTensorResolutionComputation
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N) :
    (endomorphismDerivedTensor A D E).obj ((moduleToDerived A (EndomorphismObject E)).obj N) ≅
      (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P.obj) :=
  endomorphismResolutionDerivedTensorComputation A D E
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) N ≪≫
    endomorphismProjectiveResolutionTensorIso A D E
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N) P

end SerrePositivity.DifferentialGraded
