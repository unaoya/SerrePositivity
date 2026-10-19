module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientTransitionSquare
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparisonComponents

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数表示比較の加群成分。
方針：標準制限同型を各局所点で評価し、指定単位矢の保存で underlying 遷移を比較する。
規約：canonical な比較射の同定に使い、underlying 遷移の擬同型を cartesian 条件としない。
使われ方：指定局所加群比較の表示変更の可換四角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

set_option maxHeartbeats 2000000 in
-- 三段の制限対象と標準点の値の同定に必要。
/-- 概要：係数表示の指定局所評価同型は標準点の複体で恒等。
方針：二つの標準制限合成同型の成分公式と逆元律を使う。
規約：KST §3.1。使われ方：指定局所比較の可換式で評価同型を消去する。 -/
theorem diagramCoefficientModuleEvaluationIso_hom_eval (i : J) (M : AllDiagramModules G) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      ((diagramCoefficientModuleEvaluationIso α i).hom.app M) = 𝟙 _ := by
  let H := (diagramAlgebraVertexEmbedding F i).comp (diagramCoefficientDGFunctor α)
  let A := transitionRestrictionCompIso (diagramAlgebraVertexEmbedding F i)
    (diagramCoefficientDGFunctor α) H rfl
  let B := transitionRestrictionCompIso (algebraVertexMap (α.app i))
    (diagramAlgebraVertexEmbedding G i) H (diagramCoefficientDGFunctor_vertex α i).symm
  let V := moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)
  have hA : V.map (A.hom.app M) =
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) := by
    have he := transitionRestrictionCompIso_eval
      (diagramAlgebraVertexEmbedding F i) (diagramCoefficientDGFunctor α) H rfl M .point
    change V.map (A.hom.app M) =
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) at he
    exact he
  have hB : V.map (B.hom.app M) =
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) := by
    have he := transitionRestrictionCompIso_eval
      (algebraVertexMap (α.app i)) (diagramAlgebraVertexEmbedding G i) H
      (diagramCoefficientDGFunctor_vertex α i).symm M .point
    change V.map (B.hom.app M) =
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) at he
    exact he
  have hBi : V.map (B.inv.app M) =
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) := by
    have he := congrArg V.map (B.app M).hom_inv_id
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
    change V.map (B.hom.app M) ≫ V.map (B.inv.app M) =
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) at he
    rw [hB] at he
    exact (Category.id_comp _).symm.trans he
  change V.map (A.hom.app M ≫ B.inv.app M) =
    𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩)))
  rw [CategoryTheory.Functor.map_comp, hA, hBi]
  exact Category.id_comp _

set_option maxHeartbeats 2000000 in
-- 二段の局所制限と標準点の値の同定に必要。
omit [DecidableLE J] [Small.{u} (DiagramModuleCoefficientObject F)]
  [Small.{u} (DiagramModuleCoefficientObject G)] in
/-- 概要：指定局所制限四角形の同型は標準点で恒等。
方針：同じ直接制限へ移す二つの標準合成同型を評価する。
規約：KST §3.1。使われ方：加群比較の行先の同型を具体計算で消去する。 -/
theorem diagramCoefficientModuleTransitionIso_hom_eval {i j : J} (h : i ≤ j)
    (N : ModuleCategory R (AlgebraVertex (G.obj j))ᵒᵖ) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      ((diagramCoefficientModuleTransitionIso α h).hom.app N) = 𝟙 _ := by
  let H := (diagramAlgebraVertexTransition F h).comp (algebraVertexMap (α.app j))
  let A := transitionRestrictionCompIso (diagramAlgebraVertexTransition F h)
    (algebraVertexMap (α.app j)) H rfl
  let B := transitionRestrictionCompIso (algebraVertexMap (α.app i))
    (diagramAlgebraVertexTransition G h) H (diagramCoefficientDGFunctor_transition α h).symm
  let V := moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)
  have hA : V.map (A.hom.app N) =
      𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point))) := by
    have he := transitionRestrictionCompIso_eval
      (diagramAlgebraVertexTransition F h) (algebraVertexMap (α.app j)) H rfl N .point
    change V.map (A.hom.app N) =
      𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point))) at he
    exact he
  have hB : V.map (B.hom.app N) =
      𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point))) := by
    have he := transitionRestrictionCompIso_eval
      (algebraVertexMap (α.app i)) (diagramAlgebraVertexTransition G h) H
      (diagramCoefficientDGFunctor_transition α h).symm N .point
    change V.map (B.hom.app N) =
      𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point))) at he
    exact he
  have hBi : V.map (B.inv.app N) =
      𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point))) := by
    have he := congrArg V.map (B.app N).hom_inv_id
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
    change V.map (B.hom.app N) ≫ V.map (B.inv.app N) =
      𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point))) at he
    rw [hB] at he
    exact (Category.id_comp _).symm.trans he
  change V.map (A.hom.app N ≫ B.inv.app N) =
    𝟙 ((ForgetEnrichment.to (Complex R) N).obj (op (op .point)))
  rw [CategoryTheory.Functor.map_comp, hA, hBi]
  exact Category.id_comp _

/-- 概要：係数制限は指定単位矢に沿う underlying 図式の遷移を保つ。
方針：係数 dg 関手の単位矢保存を dg 加群の作用へ合成する。
規約：KST §3.1。使われ方：canonical な局所比較の成分一致。 -/
theorem diagramCoefficientRestriction_underlying_map {i j : J} (h : i ≤ j)
    (M : AllDiagramModules G) :
    (diagramModuleUnderlyingDiagram F
        (ForgetEnrichment.to (Complex R) ((diagramCoefficientRestriction α).obj M))).map
        (homOfLE h) =
      (diagramModuleUnderlyingDiagram G (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) := by
  rw [diagramModuleUnderlyingDiagram_map, diagramModuleUnderlyingDiagram_map]
  change mapFromUnit R _ _ (diagramModuleTransitionUnit F h ≫
      (diagramCoefficientHomMap α i j ≫
        (ForgetEnrichment.to (Complex R) M).map (op (op ⟨i⟩)) (op (op ⟨j⟩)))) =
    mapFromUnit R _ _ (diagramModuleTransitionUnit G h ≫
      (ForgetEnrichment.to (Complex R) M).map (op (op ⟨i⟩)) (op (op ⟨j⟩)))
  rw [← Category.assoc, diagramCoefficientDGFunctor_unit]

end SerrePositivity.KST.DerivedBlowup
