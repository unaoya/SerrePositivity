module
public import SerrePositivity.DifferentialGraded.Morita.KernelTensor
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtension

/-! # 通常kernelの主導来作用と入力解像度の選択比較

## 概要
右D入力を射影解像して、任意の右E・左D kernelによる主導来作用を構成する。

## 方針
U10の解像度関手と選択比較を、既存のtensor dg関手のH⁰関手へ送る。

## 規約と注意
任意可換環・非有界、D・EのSmall.{u}を明示する。局所Hom K-flat条件は不要。
kernel自体の準同型局所化への降下と一般右随伴は、このファイルではまだ構成しない。

## 使われ方
U16aのkernelDerivedTensorFunctorの構成と、U16bのgraph作用比較の計算に使う。
公開契約と実装状態はformalization-plans/dg-theory-morita.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- tensorのH⁰関手を主導来局所化へ送る。準同型保存は入力を射影解像して用いる。 -/
def kernelHomotopyToDerived : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A E :=
  (kernelTensor A D E P).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 指定した任意の入力射影解像度族によるkernel作用。 -/
def kernelResolutionDerivedTensor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  moduleDerivedResolutionFunctor A D R ⋙ kernelHomotopyToDerived A D E P

/-- 標準semifree入力解像度による、通常kernelの主導来作用。 -/
def kernelDerivedTensorOnBimodule : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  kernelResolutionDerivedTensor A D E P (moduleCanonicalProjectiveResolution A D)

/-- 元の入力でH⁰計算を主局所化の計算に比較する。既存onHomotopy_facを使う。 -/
def kernelTensorHomotopyComputation (M : ModuleCategory A D) :
    (kernelHomotopyToDerived A D E P).obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) :=
  (moduleHomotopyToDerivedClosed A E).mapIso
      (eqToIso (congrArg (fun G => G.obj M) (kernelTensor A D E P).onHomotopy_fac)) ≪≫
    (moduleToHomotopyDerivedIso A E).app ((kernelTensor A D E P).onClosed.obj M)

/-- 指定解像度族の作用は、その入力解像度との通常tensorで計算できる。 -/
def kernelResolutionDerivedTensorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelResolutionDerivedTensor A D E P R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj (R M).obj) :=
  (kernelHomotopyToDerived A D E P).mapIso (moduleDerivedResolutionComputation A D R M) ≪≫
    kernelTensorHomotopyComputation A D E P (R M).obj

/-- 任意の二つの入力解像度族によるkernel作用は自然同型。 -/
def kernelResolutionDerivedTensorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionDerivedTensor A D E P R ≅ kernelResolutionDerivedTensor A D E P S :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (kernelHomotopyToDerived A D E P)

/-- 解像度族を変えないときの比較は恒等。U10の自己比較を送る。 -/
lemma kernelResolutionDerivedTensorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionDerivedTensorIso A D E P R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (kernelHomotopyToDerived A D E P).map
    ((moduleDerivedResolutionIso A D R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (kernelHomotopyToDerived A D E P).map_id _

/-- 三つの解像度族の比較は推移的。比較射を新たに選ばずU10の推移則を使う。 -/
lemma kernelResolutionDerivedTensorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    kernelResolutionDerivedTensorIso A D E P R S ≪≫
        kernelResolutionDerivedTensorIso A D E P S T =
      kernelResolutionDerivedTensorIso A D E P R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (kernelHomotopyToDerived A D E P).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (kernelHomotopyToDerived A D E P).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← Functor.map_comp]
  exact congrArg (kernelHomotopyToDerived A D E P).map
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

/-- 標準作用も、単独の任意指定入力解像度で計算できる。 -/
def kernelDerivedTensorOnBimoduleComputation {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj) := by
  let S := moduleCanonicalProjectiveResolution A D
  let e := @asIso _ _ _ _ ((moduleToHomotopy A D).map ((S M).comparison R))
    ((S M).comparison_isIso_homotopy R)
  exact (kernelHomotopyToDerived A D E P).mapIso
      (moduleDerivedResolutionComputation A D S M ≪≫ e) ≪≫
    kernelTensorHomotopyComputation A D E P R.obj

/-- graphの場合は既存の主導来延長と同じ関手。U16bの計算入口。 -/
lemma kernelDerivedTensorOnBimodule_graph (F : DGFunctor A D E) :
    kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) =
      dgDerivedExtension A D E F := rfl

end SerrePositivity.DifferentialGraded.Morita
