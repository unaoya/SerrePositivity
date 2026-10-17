module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Derived.ResolutionFunctorChoice
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.ModuleFunctorProjective

/-! # graph tensorの射影解像度による導来化と解像度選択比較

## 概要
graph tensorの射影解像度による導来化と解像度選択比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def dgExtensionHomotopyToDerived : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A E :=
  (dgModuleExtension A D E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 指定解像度族を用いる導来延長。元のHomのK-flat性は要求しない。 -/
def dgResolutionDerivedExtension
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  moduleDerivedResolutionFunctor A D R ⋙ dgExtensionHomotopyToDerived A D E F

/-- 標準semifree射影解像度を用いる導来延長。 -/
def dgDerivedExtension : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  dgResolutionDerivedExtension A D E F (moduleCanonicalProjectiveResolution A D)

def dgExtensionHomotopyComputation (M : ModuleCategory A D) :
    (dgExtensionHomotopyToDerived A D E F).obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) :=
  (moduleHomotopyToDerivedClosed A E).mapIso
      (eqToIso (congrArg (fun G => G.obj M) (dgModuleExtension A D E F).onHomotopy_fac)) ≪≫
    (moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj M)

def dgResolutionDerivedExtensionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (dgResolutionDerivedExtension A D E F R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj (R M).obj) :=
  (dgExtensionHomotopyToDerived A D E F).mapIso (moduleDerivedResolutionComputation A D R M) ≪≫
    dgExtensionHomotopyComputation A D E F (R M).obj

def dgResolutionDerivedExtensionIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    dgResolutionDerivedExtension A D E F R ≅ dgResolutionDerivedExtension A D E F S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (dgExtensionHomotopyToDerived A D E F)

lemma dgResolutionDerivedExtensionIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    dgResolutionDerivedExtensionIso A D E F R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (dgExtensionHomotopyToDerived A D E F).map
    ((moduleDerivedResolutionIso A D R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (dgExtensionHomotopyToDerived A D E F).map_id _

lemma dgResolutionDerivedExtensionIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    dgResolutionDerivedExtensionIso A D E F R S ≪≫ dgResolutionDerivedExtensionIso A D E F S T =
      dgResolutionDerivedExtensionIso A D E F R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (dgExtensionHomotopyToDerived A D E F).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (dgExtensionHomotopyToDerived A D E F).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← Functor.map_comp]
  exact congrArg (dgExtensionHomotopyToDerived A D E F).map
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

/-- 指定された任意の射影解像度でも標準導来延長を計算できる。 -/
def dgDerivedExtensionResolutionComputation {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P.obj) := by
  let R := moduleCanonicalProjectiveResolution A D
  let e := @asIso _ _ _ _ ((moduleToHomotopy A D).map ((R M).comparison P))
    ((R M).comparison_isIso_homotopy P)
  exact (dgExtensionHomotopyToDerived A D E F).mapIso
      (moduleDerivedResolutionComputation A D R M ≪≫ e) ≪≫
    dgExtensionHomotopyComputation A D E F P.obj

/-- graph tensorは射影的右加群間の準同型を保つ。相手側のflatnessは不要。 -/
lemma dgModuleExtension_projective_quasiIso
    {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) :=
  dgModuleFunctor_projective_quasiIso A D E (dgModuleExtension A D E F) hM hN f hf

end SerrePositivity.DifferentialGraded
