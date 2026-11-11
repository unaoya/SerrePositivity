module
public import SerrePositivity.KST.SConstruction.CoherentPrismCompositionFlags
public import SerrePositivity.KST.SConstruction.CoherentPathActionConstancy

/-! # 二つの定数作用から元の合成面の定数性を得る
概要：切断前後の全 Path 作用が定数なら、合成面上の元の作用も定数であることを証明する。
方針：元の豊穣合成則による厳密な分割を各高次単体で使う。
規約：元の単体の評価を保持し、合成ホモトピーを選ばない。
使われ方：上下の元の K prism の終点族を、元の二合成の定数族へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の切断前後の値が定数なら、合成面の全高次 Path の評価も定数である。 -/
lemma coherentCompositionFaceValues_eq {J : Type u} [LinearOrder J] {a b c : J}
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (R : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h₀ : ∀ (d : ℕ) (P Q : (nerve (Path a b)) _⦋d⦌),
      (R.map (.mk a) (.mk b)).app (Opposite.op ⦋d⦌) P =
        (R.map (.mk a) (.mk b)).app (Opposite.op ⦋d⦌) Q)
    (h₁ : ∀ (d : ℕ) (P Q : (nerve (Path b c)) _⦋d⦌),
      (R.map (.mk b) (.mk c)).app (Opposite.op ⦋d⦌) P =
        (R.map (.mk b) (.mk c)).app (Opposite.op ⦋d⦌) Q)
    (d : ℕ) (P Q : (nerve (Path a c)) _⦋d⦌)
    (hP : P ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).obj (Opposite.op ⦋d⦌))
    (hQ : Q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).obj (Opposite.op ⦋d⦌)) :
    (R.map (.mk a) (.mk c)).app (Opposite.op ⦋d⦌) P =
      (R.map (.mk a) (.mk c)).app (Opposite.op ⦋d⦌) Q := by
  rw [coherentPathFlag_mapping_comp R hab hbc P hP,
    coherentPathFlag_mapping_comp R hab hbc Q hQ]
  have he := congrArg₂ (fun p q => (p, q))
    (h₀ d ((coherentPathCutSplit hab hbc).app _ P).1
      ((coherentPathCutSplit hab hbc).app _ Q).1)
    (h₁ d ((coherentPathCutSplit hab hbc).app _ P).2
      ((coherentPathCutSplit hab hbc).app _ Q).2)
  exact congrArg
    ((eComp SSet (R.obj (.mk a)) (R.obj (.mk b)) (R.obj (.mk c))).app (Opposite.op ⦋d⦌)) he


/-- 合成面への制限は、同じ元の合成面の指定頂点の値の定数族そのもの。 -/
lemma coherentCompositionFaceMap_eq_const {J : Type u} [LinearOrder J] {a b c : J}
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (R : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h₀ : ∀ (d : ℕ) (P Q : (nerve (Path a b)) _⦋d⦌),
      (R.map (.mk a) (.mk b)).app (Opposite.op ⦋d⦌) P =
        (R.map (.mk a) (.mk b)).app (Opposite.op ⦋d⦌) Q)
    (h₁ : ∀ (d : ℕ) (P Q : (nerve (Path b c)) _⦋d⦌),
      (R.map (.mk b) (.mk c)).app (Opposite.op ⦋d⦌) P =
        (R.map (.mk b) (.mk c)).app (Opposite.op ⦋d⦌) Q)
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b : SSet.{u}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).ι ≫ R.map (.mk a) (.mk c) =
      SSet.const ((R.map (.mk a) (.mk c)).app (Opposite.op ⦋0⦌) p.val) := by
  apply coherentPathMap_eq_const _ p
  intro d P Q
  exact coherentCompositionFaceValues_eq R hab hbc h₀ h₁ d P.val Q.val P.property Q.property

end SerrePositivity.KST.SConstruction
