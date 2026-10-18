module

public import SerrePositivity.KST.DerivedBlowup.AlgebraVertexFunctor
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleTransitionUnit
public import SerrePositivity.KST.DerivedBlowup.GradedNaturalWhiskering

/-!
概要：KST §3.1 の dg 代数図式の正規化した局所頂点と指定遷移。
方針：モノイド対象の一対象表示を用いて係数圏へ埋め込み、指定単位矢を装備する。
規約：全 diagram-module の係数圏は構成済みのものをそのまま使う。
使われ方：元の局所模型と dg 準同値な表示での coherent な比較計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：各添字の正規表示から全図式の係数圏への dg 埋め込み。
方針：反射的包含の Hom 同定を使い、合成公式と係数関手の恒等律で積を確認する。
規約：KST §3.1。使われ方：正規表示への局所加群評価。 -/
def diagramAlgebraVertexEmbedding (i : J) :
    DGFunctor R (AlgebraVertex (F.obj i)) (DiagramModuleCoefficientObject F) where
  obj _ := ⟨i⟩
  map _ _ := diagramModuleHomInclusion F (le_refl i)
  map_id _ := rfl
  map_comp _ _ _ := by
    change MonObj.mul (X := (F.obj i).X) ≫ diagramModuleHomInclusion F (le_refl i) =
      (diagramModuleHomInclusion F (le_refl i) ⊗ₘ diagramModuleHomInclusion F (le_refl i)) ≫
        diagramModuleComp F i i i
    have hc := diagramModuleComp_on_le F (le_refl i) (le_refl i)
    rw [show F.map (homOfLE (le_refl i)) = 𝟙 (F.obj i) from F.map_id i] at hc
    simpa only [Mon.id_hom', id_tensorHom_id, Category.id_comp] using hc.symm

/-- 概要：包含に対応する正規表示間の局所 dg 遷移。
方針：係数関手の指定射を一対象表示の dg 関手へ送る。
規約：KST §3.1。使われ方：正規表示における局所制限・係数拡大。 -/
abbrev diagramAlgebraVertexTransition {i j : J} (h : i ≤ j) :=
  algebraVertexMap (F.map (homOfLE h))

omit [DecidableLE J] in
/-- 概要：正規表示の局所遷移は包含の合成を保つ。
方針：モノイド対象の射の合成保存と前順序の矢の一意性を使う。
規約：KST §3.1。使われ方：局所加群制限の標準合成同型。 -/
theorem diagramAlgebraVertexTransition_comp {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    (diagramAlgebraVertexTransition F h).comp (diagramAlgebraVertexTransition F g) =
      diagramAlgebraVertexTransition F (h.trans g) := by
  rw [diagramAlgebraVertexTransition, diagramAlgebraVertexTransition,
    algebraVertexMap_comp, ← F.map_comp]
  congr 2

omit [DecidableLE J] in
/-- 概要：正規表示の恒等包含に沿う遷移は恒等関手。
方針：係数関手と一対象表示がそれぞれ恒等射を保つことを使う。
規約：KST §3.1。使われ方：局所加群制限の単位同型。 -/
theorem diagramAlgebraVertexTransition_id (i : J) :
    diagramAlgebraVertexTransition F (le_refl i) = DGFunctor.id (AlgebraVertex (F.obj i)) := by
  change algebraVertexMap (F.map (𝟙 i)) = _
  rw [F.map_id, algebraVertexMap_id]

/-- 概要：局所埋め込みから遷移後の局所埋め込みへの指定全次数自然変換。
方針：全図式係数圏の指定単位矢と左右作用の自然性を使う。
規約：KST §3.1、パラメータは単位複体で全次数の自然性を保持する。
使われ方：正規表示での canonical な局所加群比較。 -/
def diagramAlgebraVertexTransformation {i j : J} (h : i ≤ j) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (diagramAlgebraVertexEmbedding F i)
      ((diagramAlgebraVertexTransition F h).comp (diagramAlgebraVertexEmbedding F j)) where
  app _ := diagramModuleTransitionUnit F h
  naturality _ _ := diagramModuleTransitionUnit_natural F h

end SerrePositivity.KST.DerivedBlowup
