module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：G8 の元の要素の圏の比較を、反転係数の weighted nerve まで自然に送る。
方針：元の係数同型の成分を計算し、weighted nerve の関手性と既存のラベルの自然性を使う。
規約：底の圏は固定し、元の係数同型を別の同型に置き換えない。
使われ方：IS-W1 の四角形①で、実際の unstraightening への比較の始域をそろえる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}

/-- 重みの射を、元の反転係数の射に写す。 -/
def setWeightOppositeCoefficientsMap (φ : X ⟶ Y) :
    (X ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget ⟶
      (Y ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget :=
  Functor.whiskerRight (Functor.whiskerRight φ setsToKan)
    (kanObjectOpFunctor ⋙ kanObjectForget)

/-- 元の定値係数の反転同型は、重みの実際の射と厳密に自然。 -/
lemma setWeightCoefficientsOppositeIso_naturality (φ : X ⟶ Y) :
    SetWeight.coefficientsMap φ ≫ (SetWeight.coefficientsOppositeIso Y).hom =
      (SetWeight.coefficientsOppositeIso X).hom ≫ setWeightOppositeCoefficientsMap φ := by
  ext i n x
  rfl

/-- 同じ反転係数同型の weighted nerve への像も、元の射と厳密に自然。 -/
lemma setWeightCoefficientsOppositeWeightedIso_naturality (φ : X ⟶ Y) :
    weightedNerveMap (SetWeight.coefficientsMap φ) ≫
      (SetWeight.coefficientsOppositeWeightedIso Y).hom =
    (SetWeight.coefficientsOppositeWeightedIso X).hom ≫
      weightedNerveMap (setWeightOppositeCoefficientsMap φ) := by
  change weightedNerveMap (SetWeight.coefficientsMap φ) ≫
      weightedNerveMap (SetWeight.coefficientsOppositeIso Y).hom =
    weightedNerveMap (SetWeight.coefficientsOppositeIso X).hom ≫
      weightedNerveMap (setWeightOppositeCoefficientsMap φ)
  rw [← weightedNerveMap_comp, ← weightedNerveMap_comp,
    setWeightCoefficientsOppositeIso_naturality]

/-- 元の要素の圏から反転 weighted nerve への比較は、底を変えず重みの射に自然。 -/
lemma setWeightElementsOppositeWeighted_naturality (φ : X ⟶ Y) :
    nerveMap φ.mapElements ≫ elementsToReplacement Y ≫ tautScaffold (coefficients Y) ≫
      (SetWeight.coefficientsOppositeWeightedIso Y).hom =
    (elementsToReplacement X ≫ tautScaffold (coefficients X) ≫
      (SetWeight.coefficientsOppositeWeightedIso X).hom) ≫
        weightedNerveMap (setWeightOppositeCoefficientsMap φ) := by
  have h := congrArg (fun k ↦ k ≫ (SetWeight.coefficientsOppositeWeightedIso Y).hom)
    (SetWeight.elementsWeighted_naturality φ)
  simpa only [Category.assoc, setWeightCoefficientsOppositeWeightedIso_naturality] using h

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
