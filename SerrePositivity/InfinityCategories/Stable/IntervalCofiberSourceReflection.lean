module
public import SerrePositivity.InfinityCategories.Stable.IntervalCofiberComparison
public import SerrePositivity.InfinityCategories.Stable.IntervalSuspensionReflection
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationConnecting

/-!
概要：cofiber の区間族の後二成分の可逆性から第一成分の可逆性を反映する。
方針：全区間族を一回回転し、第三成分の可逆性を懸垂図式で反映する。
規約：点ごとの回転の任意選択を自然な族として扱わない。
使われ方：任意の零角の fiber/cofiber 同値の比較辺の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：実 cofiber の区間族で後二成分が可逆なら第一成分も可逆である。
方針：関手圏で同じ loop 入力による回転を構成し、懸垂の終点評価で反映する。
規約：有限余極限や一般安定性を追加仮定にしない。
使われ方：元の零角の極限錐への比較辺を可逆とする。 -/
lemma ZeroTriangle.source_isEquivalencePath_of_middle_target {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle ((ihom (Δ[1] : SSet.{u})).obj X)) (ht : IsCofiberSequence t)
    (h₁ : IsEquivalencePathVertex (squareVertex t.square 1 0))
    (h₂ : IsEquivalencePathVertex (squareVertex t.square 1 1)) :
    IsEquivalencePathVertex (squareVertex t.square 0 0) := by
  let := hasZeroVertex_functorCategory (Δ[1] : SSet.{u}) X
  let := hasFiniteLimits_functorCategory (Δ[1] : SSet.{u}) X
  obtain ⟨r⟩ := nonempty_cofiberRotationRectangle_of_loopEquivalence
    (functorLoopSection Δ[1] s) (functorLoopSection_target s hs)
    (functorLoopSection_loop_isQCatEquivalence s hΩ) t ht
  have hsource : IsEquivalencePathVertex (squareVertex r.rotatedZeroTriangle.square 0 0) := by
    rw [r.rotated_source]
    exact h₁
  have hmiddle : IsEquivalencePathVertex (squareVertex r.rotatedZeroTriangle.square 1 0) := by
    rw [r.rotated_middle]
    exact h₂
  have htarget := r.rotatedZeroTriangle.target_isEquivalencePath_of_source_middle
    s hs hΩ r.rotated_isCofiber hsource hmiddle
  exact r.suspensionSquare.source_isEquivalencePath_of_target s hs hΩ htarget

end SerrePositivity.InfinityCategories
