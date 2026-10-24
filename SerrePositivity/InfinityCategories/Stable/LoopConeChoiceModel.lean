module
public import SerrePositivity.InfinityCategories.Stable.LoopDiagramUniversalConeModel
public import SerrePositivity.InfinityCategories.Stable.LoopConeSourceInitial
public import SerrePositivity.InfinityCategories.Core.ConeOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapIso

/-!
概要：普遍錐の選択を忘れ、全零隅四角形の始対象を得る。
方針：元の実引き戻しの同型と同じ頂点 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ固定頂点を保つ錐の比較 `loopDiagramUniversalConeIso_input`。 -/
lemma loopDiagramUniversalConeIso_input (X : SSet.{u}) [Quasicategory X] :
    (loopDiagramUniversalConeIso X).hom ≫ universalConesOverProjection
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι ≫
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι =
      loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X := by
  rw [← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ _ = _
  rw [pullback.lift_snd]
  rfl

/-- 同じ固定頂点を保つ錐の比較 `loopConeChoiceIso`。 -/
def loopConeChoiceIso (X : SSet.{u}) [Quasicategory X] :
    loopConeObjects X ≅ coneChoiceObjects
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι :=
  asIso (pullback.map (coneRestriction (horn 2 2 : SSet.{u}) X)
    (loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X)
    (coneRestriction (horn 2 2 : SSet.{u}) X)
    (universalConesOverProjection
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι ≫
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι)
    (𝟙 _) (loopDiagramUniversalConeIso X).hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using
      (loopDiagramUniversalConeIso_input X).symm))

/-- 同じ固定頂点を保つ錐の比較 `loopConeChoiceIso_diagram`。 -/
lemma loopConeChoiceIso_diagram (X : SSet.{u}) [Quasicategory X] :
    (loopConeChoiceIso X).hom ≫ pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
      (universalConesOverProjection
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι ≫
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι) = loopConeObjectDiagram X := by
  simp only [loopConeChoiceIso, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

/-- 同じ固定頂点を保つ錐の比較 `loopConeChoiceFiber_hasInitial`。 -/
lemma loopConeChoiceFiber_hasInitial {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (vertexFiber
      (pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
        (universalConesOverProjection
          (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
            IsZeroOuterCospanVertex).ι ≫
          (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
            IsZeroOuterCospanVertex).ι) ≫
        coneApexEvaluation (horn 2 2 : SSet.{u}) X) x) _⦋0⦌, IsInitialVertex v := by
  let q := pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
    (universalConesOverProjection
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι ≫
      (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
        IsZeroOuterCospanVertex).ι) ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X
  have he : (loopConeChoiceIso X).hom ≫ q = loopConeObjectSource X := by
    rw [← Category.assoc, loopConeChoiceIso_diagram]
    rfl
  let f := vertexFiberMap (loopConeObjectSource X) q (loopConeChoiceIso X).hom he x
  have : IsIso f := HomotopyLimits.vertexFiberMap_isIso _ _ _ _ _
  obtain ⟨v, hv⟩ := loopConeSourceFiber_hasInitial_of_loopEquivalence s hs hΩ x
  exact ⟨f.app (Opposite.op ⦋0⦌) v, hv.map_of_isIso f⟩
end SerrePositivity.InfinityCategories
