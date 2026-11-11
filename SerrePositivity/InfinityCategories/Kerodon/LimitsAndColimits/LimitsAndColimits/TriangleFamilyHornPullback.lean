module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleFamilyHornFromFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace

/-!
概要：元のホーンのパラメーター引き戻しと、固定 fiber への全族 curry を一般に扱う。
方針：短辺の全族自然性を使い、豊穣 nerve の実装を展開しない。
規約：標的 X は任意の単体集合。
使われ方：普遍再構成族の実ホーン fiber への登録。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleFamily_horn_pullback {X K L : SSet.{u}} {x y z : X _⦋0⦌}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y z)
    (F : (Δ[2] : SSet.{u}) ⊗ (K ⊗ L) ⟶ X)
    (a : (Λ[2, 1] : SSet.{u}) ⊗ K ⟶ X)
    (hF₂ : (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ L)) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K L ≫ f))
    (hF₀ : (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ L)) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst K L ≫ g))
    (ha₂ : (horn₂₁.ι₀₁ ▷ K) ≫ a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
    (ha₀ : (horn₂₁.ι₁₂ ▷ K) ≫ a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g) :
    ((horn 2 (1 : Fin 3)).ι ▷ (K ⊗ L)) ≫ F = ((Λ[2, 1] : SSet.{u}) ◁ fst K L) ≫ a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFamily_horn_of_faces
  · rw [hF₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
    calc
      _ = (Δ[1] ◁ fst K L) ≫ (horn₂₁.ι₁₂ ▷ K) ≫ a :=
        congrArg (fun h => (Δ[1] ◁ fst K L) ≫ h) ha₀.symm
      _ = _ := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro P
        rfl
  · rw [hF₂, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
    calc
      _ = (Δ[1] ◁ fst K L) ≫ (horn₂₁.ι₀₁ ▷ K) ≫ a :=
        congrArg (fun h => (Δ[1] ◁ fst K L) ≫ h) ha₂.symm
      _ = _ := by
        apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro P
        rfl

lemma triangleFamily_curry_horn {X K L : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ (K ⊗ L) ⟶ X)
    (a : (Λ[2, 1] : SSet.{u}) ⊗ K ⟶ X)
    (hF : ((horn 2 (1 : Fin 3)).ι ▷ (K ⊗ L)) ≫ F =
      ((Λ[2, 1] : SSet.{u}) ◁ fst K L) ≫ a) :
    curry ((α_ (Δ[2] : SSet.{u}) K L).hom ≫ F) ≫
      (pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex,
    ← Category.assoc, associator_naturality_left, Category.assoc, hF]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
