module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanWeightSimplexLift

/-!
概要：重みの単体の持ち上げは忘却と係数の添字変更を保つ。
方針：二段の Over の左成分と構造射を比較する。
規約：単体の終点を固定し、係数の始点だけを動かす。
使われ方：次数ごとの coend の降下と比較の逆の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I] {a b : I} {n : ℕ}

/-- 概要：持ち上げた鎖を忘却すると元の重みの鎖に戻る。
方針：各対象の構造射と各辺の左成分を比較する。
規約：同型ではなく関手の等式。使われ方：標準比較との一方の逆則。 -/
lemma bousfieldKanWeightSimplexLift_forget
    (σ : ComposableArrows (Over (Opposite.op a)) n) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift σ ⋙
      Over.post (Over.forget (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint σ)).op = σ := by
  refine CategoryTheory.Functor.ext (fun k ↦ ?_) ?_
  · rfl
  · intro k l f
    apply Over.OverMorphism.ext
    simp [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftArrow]

/-- 概要：係数の始点の移動は終点の Over 圏の底の射を定める。
方針：元の射 f を底の間の射に使う。
規約：重みの左成分と終点は保つ。使われ方：coend の dinaturality。 -/
def bousfieldKanWeightLiftCoefficientMap (f : a ⟶ b)
    (σ : ComposableArrows (Over (Opposite.op b)) n) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase (σ ⋙ Over.map f.op) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase σ :=
  Over.homMk f (by rfl)

/-- 概要：始点を動かした鎖の持ち上げは Over の底の後合成と一致する。
方針：元の構造射に f を前合成した式をそのまま比較する。
規約：終点の圏は同じ。使われ方：次数ごとの逆の dinaturality。 -/
lemma bousfieldKanWeightSimplexLift_coefficient (f : a ⟶ b)
    (σ : ComposableArrows (Over (Opposite.op b)) n) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift (σ ⋙ Over.map f.op) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift σ ⋙
        Over.map (bousfieldKanWeightLiftCoefficientMap f σ).op := by
  refine CategoryTheory.Functor.ext (fun k ↦ ?_) ?_
  · rfl
  · intro k l g
    apply Over.OverMorphism.ext
    simp [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftArrow]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
