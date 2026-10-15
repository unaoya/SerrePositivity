module
public import SerrePositivity.DifferentialGraded.Derived.HomOut
public import SerrePositivity.DifferentialGraded.Derived.ProjectivePrecomposition

/-! # 射影的始域の射による導来Hom関手間の自然変換

全Homの前合成を指定局所化で延長し、合成・ホモトピーとの整合性を証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 豊穣Homの表記で計算する同型。主Hom endと同じMathlib豊穣構造を使う。 -/
def moduleDerivedHomOutEnrichedComputation (T : ModuleCategory A D)
    (hT : moduleHomotopicallyProjective A D T) (N : ModuleCategory A D) :
    (moduleDerivedHomOut A D T hT).obj ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj (T ⟶[Complex A] N) :=
  eqToIso (congrArg (fun F => F.obj N) (moduleDerivedHomOut_fac A D T hT))

def moduleHomOutToDerivedPrecomp {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomOutToDerived A D N ⟶ moduleHomOutToDerived A D M :=
  Functor.whiskerRight ((eHomFunctor (Complex A) (ModuleCategory A D)).map f.op) DerivedCategory.Q

lemma moduleHomOutToDerivedPrecomp_app {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D) :
    (moduleHomOutToDerivedPrecomp A D f).app T =
      DerivedCategory.Q.map (eHomWhiskerRight (Complex A) f T) := rfl

def moduleDerivedHomOutPrecomp {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) : moduleDerivedHomOut A D N hN ⟶ moduleDerivedHomOut A D M hM :=
  Localization.Construction.natTransExtension
    (eqToHom (moduleDerivedHomOut_fac A D N hN) ≫ moduleHomOutToDerivedPrecomp A D f ≫
      eqToHom (moduleDerivedHomOut_fac A D M hM).symm)

lemma moduleDerivedHomOutPrecomp_app {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (T : ModuleCategory A D) :
    (moduleDerivedHomOutPrecomp A D hM hN f).app ((moduleToDerived A D).obj T) =
      (moduleDerivedHomOutEnrichedComputation A D N hN T).hom ≫
        DerivedCategory.Q.map (eHomWhiskerRight (Complex A) f T) ≫
          (moduleDerivedHomOutEnrichedComputation A D M hM T).inv := by
  simp only [moduleDerivedHomOutPrecomp, Localization.Construction.natTransExtension_app,
    Localization.Construction.NatTransExtension.app_eq, NatTrans.comp_app, eqToHom_app]
  rfl

lemma moduleDerivedHomOutPrecomp_id (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    moduleDerivedHomOutPrecomp A D hM hM (𝟙 M) = 𝟙 _ := by
  apply moduleDerivedNatTrans_ext A D
  intro T
  rw [moduleDerivedHomOutPrecomp_app, eHomWhiskerRight_id, CategoryTheory.Functor.map_id]
  simp

lemma moduleDerivedHomOutPrecomp_comp {M N P : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (hP : moduleHomotopicallyProjective A D P) (f : M ⟶ N) (g : N ⟶ P) :
    moduleDerivedHomOutPrecomp A D hM hP (f ≫ g) =
      moduleDerivedHomOutPrecomp A D hN hP g ≫ moduleDerivedHomOutPrecomp A D hM hN f := by
  apply moduleDerivedNatTrans_ext A D
  intro T
  rw [NatTrans.comp_app, moduleDerivedHomOutPrecomp_app, moduleDerivedHomOutPrecomp_app,
    moduleDerivedHomOutPrecomp_app, eHomWhiskerRight_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

lemma moduleDerivedHomOutPrecomp_eq_of_homotopy {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    {f g : M ⟶ N} (h : ModuleHomotopy A D f g) :
    moduleDerivedHomOutPrecomp A D hM hN f = moduleDerivedHomOutPrecomp A D hM hN g := by
  apply moduleDerivedNatTrans_ext A D
  intro T
  rw [moduleDerivedHomOutPrecomp_app, moduleDerivedHomOutPrecomp_app,
    DerivedCategory.Q_map_eq_of_homotopy (ModuleCat A) (moduleHomPrecomposeHomotopy A D h T)]

lemma moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    {f g : M ⟶ N} (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    moduleDerivedHomOutPrecomp A D hM hN f = moduleDerivedHomOutPrecomp A D hM hN g := by
  obtain ⟨h⟩ := (moduleToHomotopy_map_eq_iff A D f g).1 h
  exact moduleDerivedHomOutPrecomp_eq_of_homotopy A D hM hN h

lemma moduleDerivedHomOutPrecomp_isIso {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    IsIso (moduleDerivedHomOutPrecomp A D hM hN f) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  obtain ⟨T, rfl⟩ := (Localization.Construction.objEquiv (moduleQuasiIso A D)).surjective X
  change IsIso ((moduleDerivedHomOutPrecomp A D hM hN f).app ((moduleToDerived A D).obj T))
  rw [moduleDerivedHomOutPrecomp_app]
  have : QuasiIso (eHomWhiskerRight (Complex A) f T) :=
    moduleHomotopicallyProjective_precompose_quasiIso A D hM hN f hf T
  infer_instance

def moduleDerivedHomOutPrecompIso {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleDerivedHomOut A D N hN ≅ moduleDerivedHomOut A D M hM := by
  let : IsIso (moduleDerivedHomOutPrecomp A D hM hN f) :=
    moduleDerivedHomOutPrecomp_isIso A D hM hN f hf
  exact asIso (moduleDerivedHomOutPrecomp A D hM hN f)

end SerrePositivity.DifferentialGraded
