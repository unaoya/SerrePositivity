module
public import SerrePositivity.KST.SConstruction.PointedExtensionTransport
public import SerrePositivity.KST.SConstruction.KanAssemblyAdjoint

/-! # 入力の射をまたぐ Kan 随伴射の選択空間
概要：源の入力と標的の入力を分け、元の射への制限を保つ混合延長空間を作る。
方針：源の Kan 単位に沿う延長を使い、両端の選択空間から移送する。
規約：全次数のパラメーターと元の随伴射への制限を保持する。
使われ方：構造射の自然性を高次の相対充填へ持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 入力の射を経た元の随伴射を延長する混合選択空間。 -/
def kanAssemblyMixedChoices (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pointedExtensionSpace (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)

/-- 混合延長の選択空間も追加仮定なしに可縮 Kan。 -/
lemma kanAssemblyMixedChoices_isContractibleKan (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kanAssemblyMixedChoices r f) :=
  pointedExtensionSpace_isContractibleKan _ (Spectra.PointedKanReplacement.unit_anodyne _) _

/-- 混合延長空間の任意のパラメーター族を既存部分を保って延ばせる。 -/
lemma kanAssemblyMixedChoices_relative_lifting (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ kanAssemblyMixedChoices r f) :
    ∃ b : T ⟶ kanAssemblyMixedChoices r f, j ≫ b = a :=
  pointedExtensionSpace_relative_lifting _ (Spectra.PointedKanReplacement.unit_anodyne _) _ j a

/-- 源側の全ての選択を、標的の入力の射で後合成して混合空間へ移す。 -/
def kanAssemblyMixedFromSource (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    kanAssemblyAdjointChoices r X ⟶ kanAssemblyMixedChoices r f :=
  pointedExtensionTransport _ _ _ _ (𝟙 _) (𝟙 _) ((loopBoundaryKanFunctor (r + 1)).map f)
    (by simp) (by
      rw [Category.id_comp]
      exact ((kanTargetAssemblyAdjointNat r).naturality f).symm)

/-- 標的側の全ての選択を、源の入力の射で前合成して混合空間へ移す。 -/
def kanAssemblyMixedFromTarget (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    kanAssemblyAdjointChoices r Y ⟶ kanAssemblyMixedChoices r f :=
  pointedExtensionTransport _ _ _ _ ((oneDirectionReducedRealizationFunctor r).map f)
    ((oneDirectionKanRealizationFunctor r).map f) (𝟙 _) (by
      exact Spectra.PointedKanReplacement.unit.naturality
        ((oneDirectionReducedRealizationFunctor r).map f)) (by simp)

/-- 混合選択から元の Kan 随伴射を取り出す。 -/
def kanAssemblyMixedMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyMixedChoices r f) _⦋0⦌) :
    (oneDirectionKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj Y :=
  pointedExtensionMap _ _ v

/-- 源から移した選択の射は、元の選択の射の後合成。 -/
lemma kanAssemblyMixedFromSource_map (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    kanAssemblyMixedMap r f ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v) =
      kanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f := by
  have h := pointedExtensionTransport_vertex
    (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((kanTargetAssemblyAdjointNat r).app X)
    (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)
    (𝟙 _) (𝟙 _)
    ((loopBoundaryKanFunctor (r + 1)).map f) (by simp)
    (by rw [Category.id_comp]; exact ((kanTargetAssemblyAdjointNat r).naturality f).symm) v
  dsimp only [kanAssemblyMixedMap, kanAssemblyMixedFromSource, kanAssemblyAdjointAt]
  exact h.trans (Category.id_comp _)

/-- 標的から移した選択の射は、元の選択の射の前合成。 -/
lemma kanAssemblyMixedFromTarget_map (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    kanAssemblyMixedMap r f ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) v) =
      (oneDirectionKanRealizationFunctor r).map f ≫ kanAssemblyAdjointAt r Y v := by
  have h := pointedExtensionTransport_vertex
    (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r Y))
    ((kanTargetAssemblyAdjointNat r).app Y)
    (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)
    ((oneDirectionReducedRealizationFunctor r).map f)
    ((oneDirectionKanRealizationFunctor r).map f) (𝟙 _)
    (Spectra.PointedKanReplacement.unit.naturality
      ((oneDirectionReducedRealizationFunctor r).map f)) (by simp) v
  dsimp only [kanAssemblyMixedMap, kanAssemblyMixedFromTarget, kanAssemblyAdjointAt]
  exact h.trans (congrArg ((oneDirectionKanRealizationFunctor r).map f ≫ ·)
    (Category.comp_id (kanAssemblyAdjointAt r Y v)))

end SerrePositivity.KST.SConstruction
