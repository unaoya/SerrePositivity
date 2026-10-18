module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramRealization
public import SerrePositivity.InfinityCategories.F1.StrictTransportImageEvaluation
public import SerrePositivity.InfinityCategories.F1.StrictDiagramRealizationComparison
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningVertices

/-!
概要：strict transport の像の実現を底の対象で評価した写像の計算。
方針：底の定値図式では混合 Hom が通常の成分への射になることを使う。
規約：coherent な図式の全ての高次単体について比較する。
使われ方：Kerodon Corollary 5.6.0.6、実現写像の対象ごとの評価との整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の恒等射での混合 Hom は変換の成分写像に一致する。
方針：終域図式と内部 Hom の恒等射保存を計算する。
規約：変換の始域 F と終域 G は任意。
使われ方：Kerodon §5.3.1、底の対象を固定した対角評価。 -/
lemma strictDiagramMixedHom_base_id {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMixedHom (𝟙 c) F G = strictDiagramMappingComponent F G c := by
  rw [strictDiagramMixedHom, G.map_id, (ihom (F.obj c)).map_id, Category.comp_id]

/-- 概要：底の定値図式における対角評価は対象 c での豊穣評価になる。
方針：path の順序を取り出し、底の恒等射で混合 Hom を簡約する。
規約：添字順序 J は任意。
使われ方：Kerodon Corollary 5.6.0.6、全次数での評価の同定。 -/
lemma diagonalStrictDiagramEvaluation_constant_base
    {C J : Type u} [Category.{u} C] [LinearOrder J] (c : C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (StrictTransportDiagramObject C)) :
    diagonalStrictDiagramEvaluation ((Functor.const J).obj c) F =
      F.comp SSet (strictTransportDiagramEvaluationEnriched c) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  change (diagonalStrictDiagramHom ((Functor.const J).obj c) F i j).app n P = _
  erw [diagonalStrictDiagramHom_of_le _ F i j
    (SimplicialThickening.Path.le (P.obj 0))]
  change ((F.map i j ≫ strictDiagramMixedHom (𝟙 c)
    ((F.obj i).val ⋙ kanObjectForget) ((F.obj j).val ⋙ kanObjectForget)).app n) P = _
  rw [strictDiagramMixedHom_base_id]
  rfl

/-- 概要：実現写像を底の対象で評価すると像の coherent な評価写像を回収する。
方針：curry の頂点評価を共同評価へ戻し、底の定値図式の式を使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、実現の写像空間への作用を各対象で調べる。 -/
lemma strictTransportDiagramRealization_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    strictTransportDiagramRealization C ≫ evaluateFunctorAt (ULift.up (nerveVertex c)) =
      strictTransportDiagramInfinityEvaluation c := by
  rw [strictTransportDiagramRealization, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change diagonalStrictDiagramEvaluation
    (strictDiagramSimplexBase (PinchedHom.constant (nerveVertex c) n)) F = _
  have hbase : strictDiagramSimplexBase (PinchedHom.constant (nerveVertex c) n) =
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj c := rfl
  rw [hbase, diagonalStrictDiagramEvaluation_constant_base]
  rfl

/-- 概要：像の図式の頂点を実現すると、その Kan 値図式の coherent nerve を得る。
方針：像の代表の存在を使い、straightening の分解と既存の頂点計算を適用する。
規約：代表の選択は写像の定義に含めず、等式の証明だけに用いる。
使われ方：Kerodon Corollary 5.6.0.6、実現写像の対象への作用の計算。 -/
lemma strictTransportDiagramRealization_vertex
    {C : Type u} [Category.{u} C] (F : StrictTransportDiagramObject C) :
    (strictTransportDiagramRealization C).app (Opposite.op ⦋0⦌) (coherentNerveVertex F) =
      functorVertex (kanDiagramCoherentNerve F.val) := by
  obtain ⟨p, hp⟩ := F.property
  have hF : leftStrictTransportImageObject p = F := Subtype.ext hp
  rw [← hF, ← leftStrictTransportInfinityMap_vertex]
  change ((leftStrictTransportInfinityMap C ≫ strictTransportDiagramRealization C).app
    (Opposite.op ⦋0⦌)) (coherentNerveVertex p) = _
  rw [leftStrictTransportInfinityMap_realization]
  exact leftStraighteningCoherentMap_vertex p.val.hom

end SerrePositivity.InfinityCategories
