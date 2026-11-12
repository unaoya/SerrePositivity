module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：通常の射列の coherent な表示と豊穣関手による後合成の整合性。
方針：豊穣単位からの射を通常の射へ戻す関手を用い、定値 Hom の作用を比較する。
規約：Hom の宇宙は共有し、対象の宇宙は異なってよい。
使われ方：Kerodon §5.6（Tag 027M）、最大化した coherent な単体を通常の射列で表示する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：豊穣関手から元の通常の圏の間の関手を得る。
方針：豊穣単位からの射の圏との標準の往復を、豊穣関手の通常の作用で結ぶ。
規約：対象写像は元の豊穣関手と同じ。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な単体から取り出す通常の射列の射。 -/
def coherentEnrichedUnderlyingFunctor {C : Type v} {D : Type w}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) : C ⥤ D :=
  ForgetEnrichment.equivInverse SSet C ⋙ F.forget ⋙ ForgetEnrichment.equivFunctor SSet D

/-- 概要：豊穣関手の通常の作用の射の頂点は Hom の作用による元の頂点の像。
方針：豊穣単位からの射の全単射の往復を消し、零単体で評価する。
規約：通常の射 f を固定する。
使われ方：Kerodon §2.4.3（Tag 00KM）、定値な豊穣 Hom と後合成を比較する。 -/
lemma coherentEnrichedUnderlyingFunctor_vertex {C : Type v} {D : Type w}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {X Y : C} (f : X ⟶ Y) :
    SimplicialCategory.homEquiv' (F.obj X) (F.obj Y) ((coherentEnrichedUnderlyingFunctor F).map f) =
      (F.map X Y).app (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' X Y f) := by
  change (SSet.unitHomEquiv _) ((eHomEquiv SSet)
    ((eHomEquiv SSet).symm ((eHomEquiv SSet f) ≫ F.map X Y))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- 概要：通常の順序図式の coherent な表示は豊穣関手による後合成と可換。
方針：定値単体への作用を零単体への作用へ戻し、通常の射の頂点の式を使う。
規約：対象の宇宙が異なる豊穣関手にも適用できる。
使われ方：Kerodon §5.6（Tag 027M）、最大の区間 path による射列を元の値域に写す。 -/
lemma enrichedFunctorOfOrderDiagram_postcomp {J : Type u} [LinearOrder J]
    {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (A : J ⥤ C) (F : EnrichedFunctor SSet.{u} C D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram A).comp SSet F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (A ⋙ coherentEnrichedUnderlyingFunctor F) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change (F.map (A.obj i.as) (A.obj j.as)).app (Opposite.op ⦋d⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
      (A.map (homOfLE (SimplicialThickening.Path.le (P.obj 0))))) d) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
      ((coherentEnrichedUnderlyingFunctor F).map
        (A.map (homOfLE (SimplicialThickening.Path.le (P.obj 0)))))) d
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (F.map (A.obj i.as) (A.obj j.as))
    (SimplicialCategory.homEquiv' _ _
      (A.map (homOfLE (SimplicialThickening.Path.le (P.obj 0))))) d).trans
    (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z d)
      (coherentEnrichedUnderlyingFunctor_vertex F
        (A.map (homOfLE (SimplicialThickening.Path.le (P.obj 0)))))).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
