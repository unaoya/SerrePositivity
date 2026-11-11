module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackEndComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackEndNaturality

/-!
概要：一脚が Kan fibration の cospan の成分ごとの同値は実際の引き戻し写像を同値にする。
方針：元の pullback.map と同じ三成分で end 比較の自然性を適用する。
規約：空の入力も許す。使われ方：宇宙を持ち上げた実 fiber 模型と切断模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {L M R L' M' R' : SSet.{u}}
  [KanComplex L] [KanComplex M] [KanComplex R]
  [KanComplex L'] [KanComplex M'] [KanComplex R']
  (f : L ⟶ M) (g : R ⟶ M) (f' : L' ⟶ M') (g' : R' ⟶ M')
  [Fibration f] [Fibration f'] (s : L ⟶ L') (t : R ⟶ R') (v : M ⟶ M')
  (hs : f ≫ v = s ≫ f') (ht : g ≫ v = t ≫ g')

/-- 元の三成分が同値なら、同じ厳密な正方形の引き戻し比較自体が同値。 -/
lemma strictKanPullbackMap_homotopyEquivalence
    (es : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence s) (et : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence t)
    (ev : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (pullback.map f g f' g' s t v hs ht) := by
  let η : cospan f g ⟶ cospan f' g' := cospanHomMk v s t hs ht
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackEndComparison_detect_homotopyEquivalence f g f' g' _ η
  · rintro ⟨_ | ⟨_ | _⟩⟩
    · change pullback.map f g f' g' s t v hs ht ≫ pullback.fst f' g' ≫ f' =
        pullback.fst f g ≫ f ≫ v
      rw [← Category.assoc, pullback.map, pullback.lift_fst,
        Category.assoc, ← hs]
    · change pullback.map f g f' g' s t v hs ht ≫ pullback.fst f' g' =
        pullback.fst f g ≫ s
      simp only [pullback.map, pullback.lift_fst]
    · change pullback.map f g f' g' s t v hs ht ≫ pullback.snd f' g' =
        pullback.snd f g ≫ t
      simp only [pullback.map, pullback.lift_snd]
  · rintro (_ | ⟨_ | _⟩)
    · exact ev
    · exact es
    · exact et

end SerrePositivity.InfinityCategories.Project.FilteredExchange
