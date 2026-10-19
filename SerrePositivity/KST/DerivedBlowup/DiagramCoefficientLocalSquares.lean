module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientFunctoriality
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式射と指定局所評価の整合性。
方針：局所頂点の埋め込み、局所遷移、指定単位矢を係数 Hom の成分公式で比較する。
規約：存在する任意同型ではなく、構成済みの指定 dg 関手と単位矢を使う。
使われ方：全図式の表示比較を cartesian・局所 perfect 条件へ制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)

/-- 概要：係数 dg 関手と指定局所頂点の埋め込みは可換。
方針：反射的包含に沿う Hom の成分公式を使う。
規約：KST §3.1。使われ方：局所加群評価と表示変更の比較。 -/
theorem diagramCoefficientDGFunctor_vertex (i : J) :
    (diagramAlgebraVertexEmbedding F i).comp (diagramCoefficientDGFunctor α) =
      (algebraVertexMap (α.app i)).comp (diagramAlgebraVertexEmbedding G i) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact diagramCoefficientHomMap_inclusion α (le_refl i)

omit [DecidableLE J] in
/-- 概要：係数図式の射は正規表示の指定局所遷移と可換。
方針：一対象表示の合成保存と元の図式射の自然性を使う。
規約：KST §3.1。使われ方：局所導来制限の指定四角形。 -/
theorem diagramCoefficientDGFunctor_transition {i j : J} (h : i ≤ j) :
    (diagramAlgebraVertexTransition F h).comp (algebraVertexMap (α.app j)) =
      (algebraVertexMap (α.app i)).comp (diagramAlgebraVertexTransition G h) := by
  rw [diagramAlgebraVertexTransition, diagramAlgebraVertexTransition,
    algebraVertexMap_comp, algebraVertexMap_comp, α.naturality (homOfLE h)]

/-- 概要：係数 dg 関手は指定の包含単位矢を指定単位矢へ送る。
方針：包含上の Hom の成分とモノイド射の単位保存を使う。
規約：KST §3.1、canonical な図式加群比較を構成する単位矢を保持する。
使われ方：cartesian 条件に使う指定比較射の整合性。 -/
theorem diagramCoefficientDGFunctor_unit {i j : J} (h : i ≤ j) :
    diagramModuleTransitionUnit F h ≫ diagramCoefficientHomMap α i j =
      diagramModuleTransitionUnit G h := by
  unfold diagramModuleTransitionUnit
  rw [Category.assoc, diagramCoefficientHomMap_inclusion, ← Category.assoc,
    IsMonHom.one_hom]

end SerrePositivity.KST.DerivedBlowup
