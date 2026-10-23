module

public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementEnriched
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：taut・universal scaffold の両脚の、全変換空間に関する自然性。
方針：replacement のパラメーター移送と scaffold の可換性を全次数の族で比較する。
規約：replacement を left fibration と仮定せず、元の底上の射を厳密に保つ。
使われ方：復元 span を対象ごとの選択から全高次の共同比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- taut scaffold は、全次数の追加パラメーターを係数へ移す操作と厳密に可換。 -/
lemma tautScaffold_tensor {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    simplicialReplacementTensorMap F T ≫ tautScaffold (F ⋙ tensorRight T) =
      (tautScaffold F ▷ T) ≫ weightedNerveTensorMap F T := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨σ, τ⟩, t⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- taut scaffold は strict な変換空間全体の実際の評価と自然。 -/
lemma tautScaffold_mappingFamily {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    strictDiagramMappingReplacementEvaluation F G ≫ tautScaffold G =
      (tautScaffold F ▷ strictDiagramMappingSpace F G) ≫ weightedNerveMappingFamily F G := by
  rw [strictDiagramMappingReplacementEvaluation, Category.assoc, tautScaffold_map,
    ← Category.assoc, tautScaffold_tensor, Category.assoc]
  rfl

/-- taut scaffold の自然性を相対 Hom 全体の厳密な可換式として回収する。 -/
lemma tautScaffold_mappingSpaceMap {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    simplicialReplacementMappingSpaceMap F G ≫ HomotopyLimits.relativeFunctorPost
      (simplicialReplacementProjection G) (weightedNerveProjection G)
      (tautScaffold G) (tautScaffold_projection G) (simplicialReplacementProjection F) =
    weightedNerveMappingSpaceMap F G ≫ relativeFunctorOverPre (weightedNerveProjection G)
      (Over.homMk (U := Over.mk (simplicialReplacementProjection F))
        (V := Over.mk (weightedNerveProjection F))
        (tautScaffold F) (tautScaffold_projection F)) := by
  apply relativeFunctorUncurry_injective
  rw [relativeFunctorPost_uncurry, simplicialReplacementMappingSpaceMap_uncurry]
  have h := relativeFunctorOverPre_uncurry (weightedNerveProjection G)
    (Over.homMk (U := Over.mk (simplicialReplacementProjection F))
      (V := Over.mk (weightedNerveProjection F)) (tautScaffold F) (tautScaffold_projection F))
    (weightedNerveMappingSpaceMap F G)
  simp only [Over.homMk_left, Over.mk_left, Over.mk_hom,
    weightedNerveMappingSpaceMap_uncurry] at h
  exact (tautScaffold_mappingFamily F G).trans h.symm

/-- replacement の相対 Hom の作用を universal scaffold で後合成すると既存の評価。 -/
lemma simplicialReplacementMappingSpaceMap_scaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    simplicialReplacementMappingSpaceMap F (leftStrictTransportDiagram q) ≫
      HomotopyLimits.relativeFunctorPost
        (simplicialReplacementProjection (leftStrictTransportDiagram q)) q
        (universalScaffold q) (universalScaffold_projection q) (simplicialReplacementProjection F) =
      strictDiagramMappingScaffoldMap F q := by
  apply relativeFunctorUncurry_injective
  rw [relativeFunctorPost_uncurry, simplicialReplacementMappingSpaceMap_uncurry,
    strictDiagramMappingScaffoldMap, relativeFunctorUncurry_curry]

/-- universal scaffold は元の相対射の全空間の評価と厳密に可換。 -/
lemma universalScaffold_mappingFamily {C : Type u} [Category.{u} C]
    {E F : SSet.{u}} (p : E ⟶ nerve C) (q : F ⟶ nerve C) :
    (simplicialReplacement (leftStrictTransportDiagram p) ◁
        leftStrictTransportMappingSpaceMap p q) ≫
      strictDiagramMappingReplacementEvaluation (leftStrictTransportDiagram p)
        (leftStrictTransportDiagram q) ≫ universalScaffold q =
    (universalScaffold p ▷ relativeFunctorSpace q p) ≫
      relativeFunctorUncurry (𝟙 (relativeFunctorSpace q p)) := by
  have h := congrArg (relativeFunctorUncurry (p := q)
    (a := simplicialReplacementProjection (leftStrictTransportDiagram p)))
      (leftStrictTransportMappingSpaceMap_scaffold p q)
  rw [relativeFunctorUncurry_naturality, strictDiagramMappingScaffoldMap,
    relativeFunctorUncurry_curry] at h
  apply h.trans
  simpa only [Category.id_comp, Over.homMk_left, Over.mk_left, Over.mk_hom] using
    relativeFunctorOverPre_uncurry q
    (Over.homMk (U := Over.mk (simplicialReplacementProjection (leftStrictTransportDiagram p)))
      (V := Over.mk p) (universalScaffold p) (universalScaffold_projection p))
    (𝟙 (relativeFunctorSpace q p))

end SerrePositivity.InfinityCategories
