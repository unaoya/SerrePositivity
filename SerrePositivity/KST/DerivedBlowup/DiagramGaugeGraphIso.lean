module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeRegularIso
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Bimodule.Value

/-!
概要：KST §3.1 の包含の Hom gauge を局所遷移の graph bimodule の自己同型にする。
方針：行先の右作用と始点からの左作用の両方の整合性を gauge の合成条件から得る。
規約：全次数自然性を持つ bimodule 同型として束ねる。
使われ方：任意の cartesian 対象に対する捻りの係数拡大比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex Opposite
open DifferentialGraded CochainComplex HomComplex

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：包含の gauge は始点の係数を遷移させた左作用と可換。
方針：合成条件を第一の包含が恒等のときに適用する。
規約：KST §3.1。使われ方：graph bimodule の左作用の自然性。 -/
theorem diagramGaugeScale_leftLinear {i j : J} (h : i ≤ j) :
    (𝟙 _ ⊗ₘ (s.scale h).hom) ≫ diagramAlgebraMul (F.map (homOfLE h)) =
      diagramAlgebraMul (F.map (homOfLE h)) ≫ (s.scale h).hom := by
  have he := s.scale_comp (le_refl i) h
  rw [s.scale_id] at he
  exact he

/-- 概要：遷移後の始点斉次元との積は第二因子の gauge と可換。
方針：左作用の可換式を純 tensor で評価する。
規約：KST §3.1。使われ方：graph 左作用の各次数での計算。 -/
theorem diagramGaugeScale_left_forward {i j : J} (h : i ≤ j) {p q n : ℤ}
    (x : (F.obj i).X.X p) (y : (F.obj j).X.X q) (hn : p + q = n) :
    forward R (D := AlgebraVertex (F.obj j)) (x := .point) (y := .point) (z := .point)
        (((F.map (homOfLE h)).hom.f p) x) ((s.scale h).hom.f q y) hn =
      (s.scale h).hom.f n
        (forward R (D := AlgebraVertex (F.obj j)) (x := .point) (y := .point) (z := .point)
          (((F.map (homOfLE h)).hom.f p) x) y hn) := by
  have he := congrArg (fun f => f.f n
    (ιTensorObj (F.obj i).X (F.obj j).X p q n hn (x ⊗ₜ[R] y)))
    (diagramGaugeScale_leftLinear F s h)
  simp only [diagramAlgebraMul, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    tensorMap_apply, HomologicalComplex.id_f, ModuleCat.id_apply] at he
  exact he

/-- 概要：局所遷移の graph に対する包含 gauge の指定 bimodule 自己同型。
方針：右 regular 自己同型の族を取り、始点の作用との自然性を純斉次元で証明する。
規約：KST §3.1。使われ方：局所導来係数拡大の可逆な重み付け。 -/
def diagramGaugeGraphIso {i j : J} (h : i ≤ j) :
    BimoduleCategory.of R (AlgebraVertex (F.obj j))ᵒᵖ (AlgebraVertex (F.obj i))ᵒᵖ
        (functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op) ≅
      BimoduleCategory.of R (AlgebraVertex (F.obj j))ᵒᵖ (AlgebraVertex (F.obj i))ᵒᵖ
        (functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op) :=
  BimoduleCategory.isoOfValueFamily R _ _ (fun _ => diagramGaugeRegularIso F s h) (by
    intro b c c'
    cases b using Opposite.rec
    rename_i b
    cases b
    rw [diagramGaugeRegularIso_hom_eval]
    change ((functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).leftAt (op .point)).map c c' ≫
          homPostcompose _ (s.scale h).hom =
      ((functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).leftAt (op .point)).map c c' ≫
          homPrecompose (s.scale h).hom _
    apply hom_naturality_of_apply
    intro p f
    apply Cochain.ext
    intro r n hn
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply]
    change ((s.scale h).hom.f n)
      (((moduleHomπ R (AlgebraVertex (F.obj j))ᵒᵖ
        (representable R (op .point)) (representable R (op .point)) (op .point)).f p
        ((yonedaHom R (AlgebraVertex (F.obj j))ᵒᵖ (op .point) (op .point)).f p
          (((F.map (homOfLE h)).hom.f p) f))).v r n hn z) =
      (((moduleHomπ R (AlgebraVertex (F.obj j))ᵒᵖ
        (representable R (op .point)) (representable R (op .point)) (op .point)).f p
        ((yonedaHom R (AlgebraVertex (F.obj j))ᵒᵖ (op .point) (op .point)).f p
          (((F.map (homOfLE h)).hom.f p) f))).v r n hn (((s.scale h).hom.f r) z))
    rw [yonedaHom_element, yonedaHom_element, opposite_forward, opposite_forward]
    simp only [mul_comm r p, smul_smul, Int.units_mul_self, one_smul]
    exact (diagramGaugeScale_left_forward F s h f z (by omega)).symm)

/-- 概要：graph 自己同型の各始点対象での成分は指定 regular 自己同型。
方針：値の同型族からの bimodule 同型構成の評価公式を使う。
規約：KST §3.1。使われ方：係数拡大の重みを斉次成分で計算する。 -/
theorem diagramGaugeGraphIso_hom_eval {i j : J} (h : i ≤ j)
    (c : (AlgebraVertex (F.obj i))ᵒᵖ) :
    (BimoduleCategory.evaluation R (AlgebraVertex (F.obj j))ᵒᵖ
      (AlgebraVertex (F.obj i))ᵒᵖ c).map (diagramGaugeGraphIso F s h).hom =
        (diagramGaugeRegularIso F s h).hom :=
  BimoduleCategory.isoOfValueFamily_hom_eval R _ _ _ _ c

end SerrePositivity.KST.DerivedBlowup
