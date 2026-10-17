module
public import SerrePositivity.DifferentialGraded.Morita.KernelNaturality

/-! # 主導来kernel上の全導来tensor作用

## 概要
通常kernelの作用をkernelの準同型で局所化し、両変数が主導来対象である作用を構成する。

## 方針
射影的右D入力の相対K-flat性でkernel準同型の反転を証明し、指定bimodule局所化を使う。

## 規約と注意
局所Hom K-flat条件はこの作用に不要。D・Eは独立宇宙でSmall.{u}を明示する。
一般右随伴や合成比較の存在をここで仮定しない。

## 使われ方
U16aの主導来作用とU16b/dのgraph・Perf比較の共通入口。
受入範囲は`formalization-plans/dg-theory-m5-status.md`のU16の行に従う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- kernelの閉零射を、指定入力解像度による主導来作用の自然変換へ送る。 -/
def kernelResolutionDerivedTensorMap
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
    kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P) R ⟶
      kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P') R :=
  whiskerLeft (moduleDerivedResolutionFunctor A D R)
    (whiskerRight (kernelTensorHomotopyMap A D E f) (moduleHomotopyToDerivedClosed A E))

/-- 入力解像度での作用は恒等kernel射を恒等に送る。 -/
lemma kernelResolutionDerivedTensorMap_id
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (P : BimoduleCategory A E D) :
    kernelResolutionDerivedTensorMap A D E R (𝟙 P) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  change (moduleHomotopyToDerivedClosed A E).map
    ((kernelTensorHomotopyMap A D E (𝟙 P)).app _) = 𝟙 _
  rw [kernelTensorHomotopyMap_id]
  exact (moduleHomotopyToDerivedClosed A E).map_id _

/-- 入力解像度での作用はkernel射の合成を保つ。 -/
lemma kernelResolutionDerivedTensorMap_comp
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' P'' : BimoduleCategory A E D} (f : P ⟶ P') (g : P' ⟶ P'') :
    kernelResolutionDerivedTensorMap A D E R (f ≫ g) =
      kernelResolutionDerivedTensorMap A D E R f ≫
        kernelResolutionDerivedTensorMap A D E R g := by
  apply NatTrans.ext
  funext X
  change (moduleHomotopyToDerivedClosed A E).map
      ((kernelTensorHomotopyMap A D E (f ≫ g)).app _) =
    (moduleHomotopyToDerivedClosed A E).map ((kernelTensorHomotopyMap A D E f).app _) ≫
      (moduleHomotopyToDerivedClosed A E).map ((kernelTensorHomotopyMap A D E g).app _)
  rw [kernelTensorHomotopyMap_comp]
  exact (moduleHomotopyToDerivedClosed A E).map_comp _ _

/-- 入力解像度を通すと、任意kernel準同型の作用は全導来入力上で同型になる。 -/
lemma kernelResolutionDerivedTensorMap_isIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P')
    (hf : BimoduleCategory.quasiIso A E D f) :
    IsIso (kernelResolutionDerivedTensorMap A D E R f) := by
  let α := whiskerRight (kernelTensorHomotopyMap A D E f) (moduleHomotopyToDerivedClosed A E)
  have hbase (M : ModuleCategory A D) :
      IsIso ((kernelResolutionDerivedTensorMap A D E R f).app ((moduleToDerived A D).obj M)) := by
    have hq := kernelTensorMap_projective_quasiIso A D E f hf (R M).obj (R M).projective
    have hi : IsIso ((moduleHomotopyToDerivedClosed A E).map
        ((moduleToHomotopy A E).map ((kernelTensorMap A D E f).app (R M).obj))) :=
      Localization.inverts (moduleHomotopyToDerivedClosed A E) (moduleHomotopyQuasiIso A E) _
        ((moduleHomotopyQuasiIso_map_iff A E _).2 hq)
    have ha : IsIso (α.app ((moduleToHomotopy A D).obj (R M).obj)) := hi
    let := ha
    change IsIso (α.app ((moduleDerivedResolutionFunctor A D R).obj ((moduleToDerived A D).obj M)))
    rw [← α.naturality_2 (moduleDerivedResolutionComputation A D R M)]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let M := (moduleToDerived A D).objPreimage X
  let e := (moduleToDerived A D).objObjPreimageIso X
  have hi := hbase M
  let := hi
  rw [← (kernelResolutionDerivedTensorMap A D E R f).naturality_1 e]
  infer_instance

/-- 通常kernel全体から、主導来右加群上の作用関手への実際の関手。 -/
def kernelDerivedTensorOnBimoduleFunctor :
    BimoduleCategory A E D ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) where
  obj P := kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P)
  map f := kernelResolutionDerivedTensorMap A D E (moduleCanonicalProjectiveResolution A D) f
  map_id P := kernelResolutionDerivedTensorMap_id A D E _ P
  map_comp f g := kernelResolutionDerivedTensorMap_comp A D E _ f g

/-- 通常kernelの作用関手は、指定objectwise準同型を自然同型へ送る。 -/
lemma kernelDerivedTensorOnBimoduleFunctor_inverts :
    (BimoduleCategory.quasiIso A E D).IsInvertedBy
      (kernelDerivedTensorOnBimoduleFunctor A D E) := by
  intro P P' f hf
  exact kernelResolutionDerivedTensorMap_isIso A D E _ f hf

/-- 指定bimodule局所化上の全導来tensor作用。両変数とも主導来圏上にある。 -/
def kernelDerivedTensorFunctor :
    Kernel A D E ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) :=
  bimoduleDerivedLift A E D (kernelDerivedTensorOnBimoduleFunctor A D E)
    (kernelDerivedTensorOnBimoduleFunctor_inverts A D E)

/-- 主導来kernel上への降下は、通常kernel上の既存作用関手と可換する。 -/
lemma kernelDerivedTensorFunctor_fac :
    bimoduleToDerived A E D ⋙ kernelDerivedTensorFunctor A D E =
      kernelDerivedTensorOnBimoduleFunctor A D E :=
  bimoduleDerivedLift_fac A E D _ _

/-- 指定した任意の主導来kernelによる右加群の主導来作用。 -/
def kernelDerivedTensor (P : Kernel A D E) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  (kernelDerivedTensorFunctor A D E).obj P

/-- 通常kernelの局所化像では、全導来作用は既存の入力解像度による作用と自然同型。 -/
def kernelDerivedTensorOnBimoduleIso (P : BimoduleCategory A E D) :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P) ≅
      kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P) :=
  (eqToIso (kernelDerivedTensorFunctor_fac A D E)).app P

/-- 全導来作用を、単独の任意指定入力射影解像度による通常tensorで計算する。 -/
def kernelDerivedTensorComputation (P : Bimodule A E D) (M : ModuleCategory A D)
    (R : ModuleProjectiveResolution A D M) :
    (kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
        ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj) :=
  (kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)).app
      ((moduleToDerived A D).obj M) ≪≫
    kernelDerivedTensorOnBimoduleComputation A D E P R

end SerrePositivity.DifferentialGraded.Morita
