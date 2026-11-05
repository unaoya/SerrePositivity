module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCospanMap
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackMapComponentEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
/-!
概要：厳密可換な cospan の三成分が同値なら、元の lax pullback 比較自身が同値である。
方針：二端評価の同値持ち上げ性と三成分の引き戻し同値判定を使う。
規約：両射影と矢印族を保つ指定比較。使われ方：小模型と固定 ν 模型の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
attribute [local instance] quasicategory_tensor
lemma tensorHom_isQCatEquivalence {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    {a : A ⟶ B} {b : X ⟶ Y} (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) :
    IsQCatEquivalence (a ⊗ₘ b) := by
  letI := quasicategory_tensor A X
  letI := quasicategory_tensor B Y
  have h := (ha.isPrecompositionEquivalence.whiskerRight X).comp
    (hb.isPrecompositionEquivalence.whiskerLeft B)
  simpa only [tensorHom_def] using h.isQCatEquivalence

variable {A B C A' B' C' : SSet.{u}}
  [Quasicategory A] [Quasicategory B] [Quasicategory C]
  [Quasicategory A'] [Quasicategory B'] [Quasicategory C']
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hp : p ≫ c = a ≫ p') (hq : q ≫ c = b ≫ q')

lemma laxPullbackCospanMap_isQCatEquivalence
    (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) (hc : IsQCatEquivalence c) :
    IsQCatEquivalence (laxPullbackCospanMap p q p' q' a b c hp hq) := by
  letI := quasicategory_tensor A B
  letI := quasicategory_tensor A' B'
  letI := quasicategory_tensor C C
  letI := quasicategory_tensor C' C'
  exact pullbackMap_isQCatEquivalence_of_components
    (arrowEndpointPair C) (p ⊗ₘ q) (arrowEndpointPair C') (p' ⊗ₘ q')
    ((ihom (Δ[1] : SSet.{u})).map c) (a ⊗ₘ b) (c ⊗ₘ c)
    (arrowEndpointPair_post c) (laxPullbackCospanMap_inputs_condition p q p' q' a b c hp hq)
    (arrowEndpointPair_kanEquivalenceLifting C) (arrowEndpointPair_kanEquivalenceLifting C')
    (hc.postcompose (Δ[1] : SSet.{u}))
    (tensorHom_isQCatEquivalence ha hb)
    (tensorHom_isQCatEquivalence hc hc)

end SerrePositivity.InfinityCategories.F2
