module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeGraphIso
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparison
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor

/-!
概要：KST §3.1 の包含 gauge を局所導来係数拡大の自然自己同型へ移す。
方針：graph bimodule の指定同型を主導来 tensor 作用関手で送る。
規約：標準射影分解による既存の導来係数拡大と同じ関手を使う。
使われ方：一般の cartesian 対象に対する捻り作用の保存の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：局所遷移の導来係数拡大に対する指定 gauge 自然自己同型。
方針：左右作用と整合する graph 同型を、通常 kernel の主導来作用で送る。
規約：KST §3.1。使われ方：指定 cartesian 比較の可逆な重み付け。 -/
def diagramGaugeDerivedExtensionIso {i j : J} (h : i ≤ j) :
    diagramAlgebraDerivedExtension F h ≅ diagramAlgebraDerivedExtension F h :=
  (Morita.kernelDerivedTensorOnBimoduleFunctor R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ).mapIso
      (diagramGaugeGraphIso F s h)

/-- 概要：指定自然自己同型の順射は graph 同型の主導来 tensor 作用。
方針：関手で同型を送る構成の順射を読む。
規約：KST §3.1。使われ方：加群段階での graph 作用の計算へ戻す。 -/
theorem diagramGaugeDerivedExtensionIso_hom {i j : J} (h : i ≤ j) :
    (diagramGaugeDerivedExtensionIso F s h).hom =
      (Morita.kernelDerivedTensorOnBimoduleFunctor R
        (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ).map
          (diagramGaugeGraphIso F s h).hom := rfl

end SerrePositivity.KST.DerivedBlowup
