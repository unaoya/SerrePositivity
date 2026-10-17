module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelColimits
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentation
public import SerrePositivity.DifferentialGraded.Verdier.DerivedCoproductComparison

/-! # 任意の主導来kernel作用の余積保存

## 概要
任意kernelの実際の主導来作用がu-small余積を保存することを証明する。

## 方針
射影的な入力族とその余積で増大比較を反転し、既存の主局所化の余積保存へ帰着する。
任意の導来族は指定射影解像度の族へ比較する。

## 規約と注意
kernelの列の射影性・局所Hom K-flat性を仮定しない。射影性は入力の計算モデルだけに使う。
対象宇宙は独立で、余積添字はSmall.{u}。

## 使われ方
U16aの一般右随伴を構成する生成元被覆・関係除去・可算telescopeへ実際の余積保存を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  {J : Type z} [Small.{u} J]

/-- 射影入力族の導来余積を作用で写したcofanは、出力側でも余積。 -/
def kernelDerivedTensorProjectiveCofanIsColimit (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    IsColimit ((kernelDerivedTensorOnBimodule A D E P).mapCocone
      (moduleProjectiveDerivedCofan A D M)) := by
  let T := kernelDerivedTensorOnBimodule A D E P
  let G := (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E
  let η := kernelDerivedTensorAugmentation A D E P
  let C := G.mapCocone (colimit.cocone (Discrete.functor M))
  let e : Discrete.functor (fun j => (moduleToDerived A D).obj (M j)) ⋙ T ≅
      Discrete.functor M ⋙ G :=
    Discrete.natIso (fun j => by
      have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P (M j.as)
        (moduleHomotopicallyProjective_relativeKFlat A D (hM j.as))
      exact asIso (η.app (M j.as)))
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P (∐ M)
    (moduleHomotopicallyProjective_relativeKFlat A D
      (moduleCoproduct_homotopicallyProjective A D M hM))
  let ep := asIso (η.app (∐ M))
  have hC : IsColimit C := isColimitOfPreserves G (coproductIsCoproduct M)
  have hp := (IsColimit.precomposeHomEquiv e C).symm hC
  refine IsColimit.ofIsoColimit hp (Cocone.ext ep ?_).symm
  rintro ⟨j⟩
  exact η.naturality (Sigma.ι M j)

/-- 通常kernelの導来作用は、射影入力族の主導来像の余積を保存する。 -/
lemma kernelDerivedTensorPreservesProjectiveCoproduct (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    PreservesColimit (Discrete.functor (fun j => (moduleToDerived A D).obj (M j)))
      (kernelDerivedTensorOnBimodule A D E P) :=
  preservesColimit_of_preserves_colimit_cocone
    (moduleProjectiveDerivedCofanIsColimit A D M hM)
    (kernelDerivedTensorProjectiveCofanIsColimit A D E P M hM)

/-- 任意の導来入力族を射影解像度の族へ比較して、余積保存を得る。 -/
instance kernelDerivedTensorOnBimodulePreservesCoproduct (F : J → DerivedModuleCategory A D) :
    PreservesColimit (Discrete.functor F) (kernelDerivedTensorOnBimodule A D E P) := by
  let R := fun j => moduleCanonicalProjectiveResolution A D (F j).as.obj
  let M := fun j => (R j).obj
  let := kernelDerivedTensorPreservesProjectiveCoproduct A D E P M (fun j => (R j).projective)
  let e : Discrete.functor (fun j => (moduleToDerived A D).obj (M j)) ≅ Discrete.functor F :=
    Discrete.natIso (fun j => moduleDerivedIso A D (R j.as).π (R j.as).quasiIso)
  exact preservesColimit_of_iso_diagram (kernelDerivedTensorOnBimodule A D E P) e

/-- 任意通常kernelの主導来作用はu-small余積を保存する。 -/
instance kernelDerivedTensorOnBimodulePreservesCoproducts :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensorOnBimodule A D E P) :=
  preservesColimitsOfShape_of_discrete _

/-- 主局所化上の任意kernelの作用もu-small余積を保存する。 -/
lemma kernelDerivedTensorPreservesCoproducts (K : Kernel A D E) :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K) := by
  obtain ⟨⟨Q⟩⟩ := K
  exact preservesColimitsOfShape_of_natIso (kernelDerivedTensorOnBimoduleIso A D E Q).symm

end SerrePositivity.DifferentialGraded.Morita
