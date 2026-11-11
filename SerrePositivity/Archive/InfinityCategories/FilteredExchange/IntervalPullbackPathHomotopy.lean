module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPath
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackHomotopyPoint

/-!
概要：元の区間引き戻しの全 path 座標を二射影の間の指定ホモトピーとして読む。
方針：置換の path 円柱を第一射影で制限し、終点を引き戻し条件で同定する。
規約：全 path を保持。使われ方：native な錐の可換性と元の path の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- 概要：元の二射影の像を結ぶ指定された全 path 円柱。
方針：元の path を uncurry。規約：新たな代表を選ばない。使われ方：二次の整合。 -/
def intervalPullbackPathHomotopy :
    SSet.Homotopy (intervalPullbackLeft f g ≫ f) (intervalPullbackRight f g ≫ g) where
  h := (intervalReplacementPathHomotopy f (pullback.fst (intervalReplacementEndpoint f) g)).h
  h₀ := (intervalReplacementPathHomotopy f (pullback.fst (intervalReplacementEndpoint f) g)).h₀
  h₁ := (intervalReplacementPathHomotopy f
    (pullback.fst (intervalReplacementEndpoint f) g)).h₁.trans pullback.condition
  rel := (intervalReplacementPathHomotopy f (pullback.fst (intervalReplacementEndpoint f) g)).rel

/-- 概要：指定円柱を curry すると元の全 path 座標そのもの。
方針：元の置換円柱の往復。規約：射の厳密な式。使われ方：元の path の識別。 -/
lemma intervalPullbackPathHomotopy_curry :
    curry ((β_ (Δ[1] : SSet.{u}) (intervalPullback f g)).hom ≫
      (intervalPullbackPathHomotopy f g).h) = intervalPullbackPath f g :=
  intervalReplacementPathHomotopy_curry f (pullback.fst (intervalReplacementEndpoint f) g)

/-- 概要：元の二射影と指定円柱で復元した引き戻しの自己射は恒等射。
方針：三座標を厳密に照合。規約：全 path を保持。使われ方：指定データの最終同定。 -/
lemma intervalPullbackHomotopyPoint_pathHomotopy :
    intervalPullbackHomotopyPoint f g (intervalPullbackLeft f g) (intervalPullbackRight f g)
      (intervalPullbackPathHomotopy f g) = 𝟙 (intervalPullback f g) := by
  apply intervalPullback_hom_ext
  · rw [intervalPullbackHomotopyPoint_path, intervalPullbackPathHomotopy_curry, Category.id_comp]
  · rw [intervalPullbackHomotopyPoint_left, Category.id_comp]
  · rw [intervalPullbackHomotopyPoint_right, Category.id_comp]

/-- 概要：元の path 円柱のホモトピー類を二射影の可換同型にする。
方針：Kan 標的での指定辺の可逆性。規約：元の辺の類。使われ方：錐の可換性の照合。 -/
def intervalPullbackPathIso [KanComplex Y] :
    FunctorIso (intervalPullbackLeft f g ≫ f) (intervalPullbackRight f g ≫ g) := by
  have : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (intervalPullbackPathHomotopy f g)) :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (intervalPullbackPathHomotopy f g)))

/-- 概要：指定可換同型の順方向の射は元の全 path 円柱の類。
方針：asIso の定義。規約：代表を選び直さない。使われ方：最終整合式の指定値。 -/
lemma intervalPullbackPathIso_hom [KanComplex Y] :
    (intervalPullbackPathIso f g).hom = SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (intervalPullbackPathHomotopy f g)) := rfl

end SerrePositivity.InfinityCategories.F2
