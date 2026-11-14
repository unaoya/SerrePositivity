module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.MappingPathNaturality

/-!
概要：Kan fibration に沿って自由 path を指定端点とともに相対的に持ち上げる。
方針：端点包含の anodyne 性を点つき Hom の相対充填へ渡し、単位の同型で端点を表示する。
規約：任意の単射パラメータと両端点を扱う。
使われ方：Goerss–Jardine I §7、BF 1978 §2、mapping path の塔の相対 RLP。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：自由 path の単射パラメータ上の族を、指定端点と底への path を保って拡張できる。
方針：anodyne な端点包含に沿う点つき Hom の相対充填を使う。
規約：標的の射 p の fibration 性を要求し、両端点のどちらも選べる。
使われ方：mapping path の塔から源への射の相対比較の全ての単射への RLP。 -/
lemma relativeFreePath_lift {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) [Fibration p.right] (k : Fin 2)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) (b : U ⟶ Y.right)
    (c : U ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Z).right)
    (hc : j ≫ b = a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y k).right)
    (he : a ≫ (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} p).right = j ≫ c)
    (ha : b ≫ p.right = c ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Z k).right) :
    ∃ l : U ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right, j ≫ l = a ∧
      l ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y k).right = b ∧
      l ≫ (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} p).right = c := by
  let eY := PointedSimplicialSet.forget.mapIso (unitIsoSelf (X := Y))
  let eZ := PointedSimplicialSet.forget.mapIso (unitIsoSelf (X := Z))
  have hendY : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k) Y ≫ eY.hom =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y k).right := rfl
  have hendZ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k) Z ≫ eZ.hom =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Z k).right := rfl
  have hu : (PointedObject.basedHomMap (𝟙_ PointedSimplicialSet.{u}) p).right ≫ eZ.hom =
      eY.hom ≫ p.right := by
    exact congrArg Under.Hom.right ((unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality p)
  have hc' : j ≫ (b ≫ eY.inv) = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k) Y := by
    apply (cancel_mono eY.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, hendY] using hc
  have ha' : (b ≫ eY.inv) ≫
      (PointedObject.basedHomMap (𝟙_ PointedSimplicialSet.{u}) p).right =
        c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k) Z := by
    apply (cancel_mono eZ.hom).mp
    simpa only [Category.assoc, hu, Iso.inv_hom_id_assoc, hendZ] using ha
  obtain ⟨l, hl, hpre, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePointedHom_anodyneLift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_anodyne k) p j a (b ≫ eY.inv) c hc' he ha'
  refine ⟨l, hl, ?_, hp⟩
  rw [← hendY, ← Category.assoc, hpre, Category.assoc, eY.inv_hom_id]
  change b ≫ 𝟙 Y.right = b
  exact Category.comp_id _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
