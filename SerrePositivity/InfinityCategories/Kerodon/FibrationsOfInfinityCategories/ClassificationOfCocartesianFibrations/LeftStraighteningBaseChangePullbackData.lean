module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange

/-!
概要：初頂点への制限と底変換を交換する指定pullbackを、同じ二座標から構成する。
方針：標準pullbackの貼り合わせ・消去と、uliftによるpullbackの保存を使う。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の構成の前提計算。
  任意の比較射やそのpullback性を仮定せず、指定座標のpullback.liftを使う。
使われ方：S8のP3-C0、表現の底変換と単体圏への制限の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
noncomputable section

/-- 元の二座標の標準比較と、元の宇宙およびulift後のpullback性。
HTT §3.3.2の底変換の構成に付随する法則の、この単体圏模型での特殊化。 -/
@[cite HTT "3.3.2" (partial := special) "初頂点と底変換の指定二座標pullbackの計算。"]
def leftStraighteningBaseChangePullbackData
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    { t : pullback q lD ⟶ pullback p lB //
      t ≫ pullback.fst p lB = pullback.fst q lD ≫ pullback.fst p k ∧
      t ≫ p₀ = r ≫ nerveMap H ∧
      IsPullback t r p₀ (nerveMap H) ∧
      IsPullback (U.map t) (U.map r) (U.map p₀) (U.map (nerveMap H)) } := by
  dsimp only
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let b := nerveMap (transportSimplexFunctor k)
  let q := pullback.snd p k
  let r := pullback.snd q lD
  let e := pullback.fst q lD ≫ pullback.fst p k
  have hw : e ≫ p = (r ≫ b) ≫ lB := by
    dsimp only [e, r, b, lB, lD, q]
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, ← transportSimplexFirstVertexMap_naturality k, ← Category.assoc]
  let t := pullback.lift e (r ≫ b) hw
  have ht₁ : t ≫ pullback.fst p lB = e := pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd p lB = r ≫ b := pullback.lift_snd _ _ _
  have hwide := (IsPullback.of_hasPullback q lD).paste_horiz (IsPullback.of_hasPullback p k)
  have ho : IsPullback (t ≫ pullback.fst p lB) r p (b ≫ lB) := by
    rw [ht₁]
    simpa only [b, lB, lD, transportSimplexFirstVertexMap_naturality k] using hwide
  have ht := ho.of_right ht₂ (IsPullback.of_hasPullback p lB)
  have : PreservesLimitsOfShape WalkingCospan (SSet.uliftFunctor.{u+1,u}) := by
    apply preservesLimitsOfShape_of_evaluation
    intro n
    change PreservesLimitsOfShape WalkingCospan
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n ⋙ CategoryTheory.uliftFunctor)
    infer_instance
  exact ⟨t, ht₁, ht₂, ht, ht.map _⟩
end
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
