module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletonFiltration
public import SerrePositivity.KST.Spectra.PointedWeightedEndPreMap

/-!
概要：重みの有限骨格による点つき end の塔と、全体の end からの錐。
方針：重みの骨格の包含を点つき end の反変関手へ送る。
規約：通常の n 骨格を使う。この段階では塔の fibration 性と収束をまだ主張しない。
使われ方：Goerss–Jardine VIII §1。Tot の塔の段階的な解析。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet Opposite

namespace SerrePositivity.KST.Spectra.SkeletalWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：重みの値を通常の n 骨格へ制限する。
方針：Mathlib の skeleton (n+1) の関手を後合成する。
規約：n は含める単体の最大次元。
使われ方：Goerss–Jardine VIII §1。部分 end の重み。 -/
def weight (W : I ⥤ SSet.{u}) (n : ℕ) : I ⥤ SSet.{u} :=
  W ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor (n + 1)

/-- 概要：重みの有限骨格の間の包含。
方針：骨格関手の間の自然変換を重みで前合成する。
規約：n≤m の向きに重みが増える。
使われ方：Goerss–Jardine VIII §1。部分 end の塔の遷移。 -/
def weightTransition (W : I ⥤ SSet.{u}) {n m : ℕ} (h : n ≤ m) :
    weight W n ⟶ weight W m :=
  Functor.whiskerLeft W (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.transition (Nat.add_le_add_right h 1))

/-- 概要：有限骨格の重みから全体の重みへの包含。
方針：骨格の包含の自然変換を重みで前合成する。
規約：値は実際の部分複体の包含。
使われ方：Goerss–Jardine VIII §1。全体から部分 end への制限。 -/
def weightInclusion (W : I ⥤ SSet.{u}) (n : ℕ) : weight W n ⟶ W :=
  Functor.whiskerLeft W (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.inclusion (n + 1))

lemma weightTransition_inclusion (W : I ⥤ SSet.{u}) {n m : ℕ} (h : n ≤ m) :
    weightTransition W h ≫ weightInclusion W m = weightInclusion W n := rfl

/-- 概要：有限骨格の重みを自然数に沿う増加図式に束ねる。
方針：部分複体の包含の恒等と合成を使う。
規約：自然数を通常の順序圏として使う。
使われ方：Goerss–Jardine VIII §1。塔の反対向きの重みの図式。 -/
def weightDiagram (W : I ⥤ SSet.{u}) : ℕ ⥤ (I ⥤ SSet.{u}) where
  obj n := weight W n
  map f := weightTransition W (leOfHom f)
  map_id n := by
    apply NatTrans.ext
    funext i
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext i
    rfl

/-- 概要：有限骨格の重みによる点つき end の塔。
方針：増加する重みを前合成の反変関手へ送る。
規約：係数 D は固定する。Kan 条件を定義には要求しない。
使われ方：Goerss–Jardine VIII §1。Tot の段と遷移の模型。 -/
def tower (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    ℕᵒᵖ ⥤ PointedSimplicialSet.{u} :=
  (weightDiagram W).op ⋙ PointedWeightedEnd.weightFunctor D

/-- 概要：有限骨格の増加図式から全体の重みへの余錐。
方針：骨格の包含を自然変換の余錐に束ねる。
規約：通常の関手圏の余錐。
使われ方：Goerss–Jardine VIII §1。全体の end への反変な制限の入力。 -/
def weightCocone (W : I ⥤ SSet.{u}) : Cocone (weightDiagram W) where
  pt := W
  ι := {
    app n := weightInclusion W n
    naturality n m f := by
      change weightTransition W (leOfHom f) ≫ weightInclusion W m =
        weightInclusion W n ≫ 𝟙 W
      rw [Category.comp_id, weightTransition_inclusion] }

/-- 概要：全体の重み付き end から有限骨格の end の塔への錐。
方針：骨格の包含で前合成し、前合成の合成則で整合性を示す。
規約：この宣言だけでは錐の極限性を主張しない。
使われ方：Goerss–Jardine VIII §1。全体と有限段の比較。 -/
def cone (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) : Cone (tower W D) :=
  (PointedWeightedEnd.weightFunctor D).mapCone (weightCocone W).op

end

end SerrePositivity.KST.Spectra.SkeletalWeightedEnd
