module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeParameterPrism

/-!
概要：頂点が動く native な余錐の族を元の図式の円柱として評価する。
方針：coslice の元の join 表示を円柱で制限する。
規約：終点固定の fiber を取らず、可変頂点の全情報を残す。
使われ方：全 Hom 輸送による余錐の変換の正方形。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {K X T U : SSet.{u}} {f : K ⟶ X}

/-- 概要：可変頂点の余錐の全族を円柱上で評価する。
方針：元の join 表示をそのまま制限する。
規約：図式 f は固定。使われ方：指定余錐の変換の全族。 -/
def coconeVariablePrism (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder f) : (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap K T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a

/-- 概要：可変頂点の族も始点では元の図式に固定される。
方針：join の左包含で評価する。規約：全族。使われ方：正方形の固定辺。 -/
lemma coconeVariablePrism_zero (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder f) :
    (SSet.ι₀ ▷ T) ≫ coconeVariablePrism a = fst K T ≫ f := by
  rw [coconeVariablePrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]

/-- 概要：可変頂点の円柱の終点は元の族の頂点の射影。
方針：join の右包含で評価する。規約：定値性を要求しない。使われ方：輸送の底の辺。 -/
lemma coconeVariablePrism_one (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder f) :
    (SSet.ι₁ ▷ T) ≫ coconeVariablePrism a = snd K T ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection f := by
  rw [coconeVariablePrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]

/-- 概要：可変頂点の円柱は任意のパラメータの前合成と可換。
方針：join の円柱と coslice の uncurry の自然性を使う。
規約：全時刻での等式。使われ方：正方形の二辺の照合。 -/
lemma coconeVariablePrism_precomp (i : T ⟶ U) (a : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder f) :
    coconeVariablePrism (i ≫ a) =
      ((K ⊗ (Δ[1] : SSet.{u})) ◁ i) ≫ coconeVariablePrism a := by
  rw [coconeVariablePrism, coconeVariablePrism, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    ← Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality (𝟙 K) i
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap, id_whiskerRight, id_tensorHom, Category.assoc] using
    congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry a) h.symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
