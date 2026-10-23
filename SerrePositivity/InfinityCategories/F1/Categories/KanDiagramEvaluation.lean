module

public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramRealization
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition

/-!
概要：一般の strict な Kan 値図式の共同評価と対象での評価の整合性。
方針：底の定値図式を代入し、混合 Hom を成分の評価へ戻す。
規約：図式の変換空間に Kan 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、豊穣自然変換の coherent な実現の端点の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：strict な Kan 値図式を指定した底の対象で評価する豊穣関手。
方針：strict な変換の対象成分を Hom の作用とし、成分での単位・合成の計算則を使う。
規約：標的は coherent nerve を取る前の KanObject の単体的圏。
使われ方：Kerodon §5.3.1、Corollary 5.6.0.6、coherent な評価を作る豊穣的な入力。 -/
def kanDiagramEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (KanDiagramObject C) KanObject.{u} where
  obj F := F.val.obj c
  map F G := strictDiagramMappingComponent (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) c
  map_id F := strictDiagramMappingIdentity_component (F.val ⋙ kanObjectForget) c
  map_comp F G H := strictDiagramMappingComposition_component
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) (H.val ⋙ kanObjectForget) c

/-- 概要：strict な Kan 値図式の coherent nerve から 𝒮 への対象ごとの評価関手。
方針：対象ごとの豊穣評価に coherent nerve を適用する。
規約：元の図式の対象と高次の変換の族を同じ評価で扱う。
使われ方：Kerodon Corollary 5.6.0.6、関手 ∞ 圏への比較を値で検証する評価射。 -/
noncomputable def kanDiagramNerveEvaluation {C : Type u} [Category.{u} C] (c : C) :
    KanDiagramNerve C ⟶ SpaceInfinity.{u} :=
  coherentNerveMap (kanDiagramEvaluationEnriched c)

/-- 概要：底の恒等射での混合 Hom は変換の成分写像に一致する。
方針：終域図式と内部 Hom の恒等射保存を計算する。
規約：変換の始域 F と終域 G は任意。
使われ方：Kerodon §5.3.1、底の対象を固定した対角評価。 -/
lemma kanDiagramMixedHom_base_id {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMixedHom (𝟙 c) F G = strictDiagramMappingComponent F G c := by
  rw [strictDiagramMixedHom, G.map_id, (ihom (F.obj c)).map_id, Category.comp_id]

/-- 概要：底の定値図式における対角評価は対象 c での豊穣評価になる。
方針：path の順序を取り出し、底の恒等射で混合 Hom を簡約する。
規約：添字順序 J は任意。
使われ方：Kerodon Corollary 5.6.0.6、全次数での評価の同定。 -/
lemma diagonalKanDiagramEvaluation_constant_base
    {C J : Type u} [Category.{u} C] [LinearOrder J] (c : C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (KanDiagramObject C)) :
    diagonalKanDiagramEvaluation ((Functor.const J).obj c) F =
      F.comp SSet (kanDiagramEvaluationEnriched c) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  change (diagonalKanDiagramHom ((Functor.const J).obj c) F i j).app n P = _
  erw [diagonalKanDiagramHom_of_le _ F i j
    (SimplicialThickening.Path.le (P.obj 0))]
  change ((F.map i j ≫ strictDiagramMixedHom (𝟙 c)
    ((F.obj i).val ⋙ kanObjectForget) ((F.obj j).val ⋙ kanObjectForget)).app n) P = _
  rw [kanDiagramMixedHom_base_id]
  rfl

/-- 概要：実現写像を底の対象で評価すると図式の coherent な評価写像を回収する。
方針：curry の頂点評価を共同評価へ戻し、底の定値図式の式を使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、実現の写像空間への作用を各対象で調べる。 -/
lemma kanDiagramRealization_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    kanDiagramRealization C ≫ evaluateFunctorAt (ULift.up (nerveVertex c)) =
      kanDiagramNerveEvaluation c := by
  rw [kanDiagramRealization, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change diagonalKanDiagramEvaluation
    (kanDiagramSimplexBase (PinchedHom.constant (nerveVertex c) n)) F = _
  have hbase : kanDiagramSimplexBase (PinchedHom.constant (nerveVertex c) n) =
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj c := rfl
  rw [hbase, diagonalKanDiagramEvaluation_constant_base]
  rfl

end SerrePositivity.InfinityCategories
