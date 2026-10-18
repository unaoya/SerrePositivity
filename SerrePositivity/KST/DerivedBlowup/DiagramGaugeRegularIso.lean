module

public import SerrePositivity.KST.DerivedBlowup.DiagramHomGauge
public import SerrePositivity.KST.DerivedBlowup.AlgebraVertex
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.RestrictionAction

/-!
概要：KST §3.1 の Hom gauge を局所 regular 加群の自己同型にする。
方針：合成条件を恒等包含に特殊化し、目標代数の右作用との整合性を取り出す。
規約：基底環上の dg 加群として全次数の自然性を証明する。
使われ方：捻りの canonical な係数拡大比較を regular 比較へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：各包含の Hom gauge は行先の代数の右作用と可換。
方針：合成保存を第二の包含が恒等のときに適用する。
規約：KST §3.1。使われ方：局所 regular 加群の自己同型の自然性。 -/
theorem diagramGaugeScale_rightLinear {i j : J} (h : i ≤ j) :
    ((s.scale h).hom ⊗ₘ 𝟙 _) ≫ MonObj.mul =
      MonObj.mul ≫ (s.scale h).hom := by
  have he := s.scale_comp h (le_refl j)
  rw [s.scale_id, show F.map (homOfLE (le_refl j)) = 𝟙 (F.obj j) from F.map_id j,
    diagramAlgebraMul_id] at he
  exact he

/-- 概要：局所斉次積の最初の因子の gauge は積の gauge に一致する。
方針：右作用の可換式を純 tensor 上で評価する。
規約：KST §3.1。使われ方：代表加群の全次数作用の可換式。 -/
theorem diagramGaugeScale_forward {i j : J} (h : i ≤ j) {p q n : ℤ}
    (x : (F.obj j).X.X p) (y : (F.obj j).X.X q) (hn : p + q = n) :
    forward R (D := AlgebraVertex (F.obj j)) (x := .point) (y := .point) (z := .point)
      ((s.scale h).hom.f p x) y hn =
      (s.scale h).hom.f n
        (forward R (D := AlgebraVertex (F.obj j)) (x := .point) (y := .point) (z := .point)
          x y hn) := by
  have he := congrArg (fun f => f.f n
    (ιTensorObj (F.obj j).X (F.obj j).X p q n hn (x ⊗ₜ[R] y)))
    (diagramGaugeScale_rightLinear F s h)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, tensorMap_apply,
    HomologicalComplex.id_f,
    ModuleCat.id_apply] at he
  exact he

/-- 概要：包含の Hom gauge は行先の局所 regular dg 加群の指定自己同型を与える。
方針：右作用可換式を代表加群の作用へ読み替え、全次数同型族から構成する。
規約：KST §3.1。使われ方：canonical な捻り遷移の局所比較。 -/
def diagramGaugeRegularIso {i j : J} (h : i ≤ j) :
    ForgetEnrichment.of (Complex R)
        (representable R (op (.point : AlgebraVertex (F.obj j)))) ≅
      ForgetEnrichment.of (Complex R)
        (representable R (op (.point : AlgebraVertex (F.obj j)))) :=
  moduleIsoMk R (AlgebraVertex (F.obj j))ᵒᵖ (fun _ => s.scale h) (by
    apply closedFamily_of_action
    intro x y p r n hn f z
    rw [representable_action, representable_action, opposite_forward, opposite_forward]
    change ((s.scale h).hom.f n).hom ((p * r).negOnePow •
        forward R (D := AlgebraVertex (F.obj j)) (x := .point) (y := .point) (z := .point)
          z f (by omega)) =
      (p * r).negOnePow • forward R (D := AlgebraVertex (F.obj j))
        (x := .point) (y := .point) (z := .point) ((s.scale h).hom.f r z) f (by omega)
    simp only [Units.smul_def, map_zsmul]
    rw [diagramGaugeScale_forward])

/-- 概要：局所 regular 自己同型の標準点成分は指定 Hom gauge。
方針：全次数同型族からの構成の評価公式を使う。
規約：KST §3.1。使われ方：局所生成元の像と導来比較を照合する。 -/
theorem diagramGaugeRegularIso_hom_eval {i j : J} (h : i ≤ j) :
    (moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
      (diagramGaugeRegularIso F s h).hom = (s.scale h).hom :=
  moduleIsoMk_hom_eval R _ _ _ _

end SerrePositivity.KST.DerivedBlowup
