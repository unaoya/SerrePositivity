module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomLiftingEquiv
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFamilyAssembly

/-!
概要：fiber の普遍余錐を用いて相対 join の逆像上の実際の図式を延長する。
方針：図式を族へ移し、相対骨格で延長した後、二つの固定条件を保って戻す。
規約：パラメータは任意の単体集合、底と値域は quasicategory。
使われ方：Kerodon Lemma 7.3.4.5–6 の図式の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：普遍余錐の頂点条件があれば、元の図式と部分上の図式を同時に保つ延長が存在する。
方針：制限の自然性で族の可換四角形を作り、余極限からの延長を uncurry する。
規約：欠けた各単体の最初の頂点で普遍余錐の表示を指定する。
使われ方：相対 join 上の Kan 拡張を実際の単体集合の射として組み立てる。 -/
lemma exists_kanRelativeJoin_diagram_extension_of_colimits {K C D A : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (c : A ⟶ C) (A₀ : A.Subcomplex)
    (hA₀ : ∀ v : A _⦋0⦌, v ∈ A₀.obj (Opposite.op ⦋0⦌))
    (F : pullback c p ⟶ D)
    (G : pullback (A₀.ι ≫ c) (relativeJoinBaseProjection p (𝟙 C)) ⟶ D)
    (hFG : (overPullbackUnderlying p).map
      (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ F =
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk (A₀.ι ≫ c)) ≫ G)
    (hcol : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      ∃ (v : C _⦋0⦌) (d : vertexFiber p v ⟶ D) (z : JoinCocone d),
        IsColimitCone z ∧
        (((kanRelativeJoinCoconeFiberIso p v D).hom.app (Opposite.op ⦋0⦌)
          (functorVertex z.val)).val) =
          (kanFiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G).app
            (Opposite.op ⦋0⦌) ⟨simplexFirstVertex σ, hA₀ _⟩) :
    ∃ H : pullback c (relativeJoinBaseProjection p (𝟙 C)) ⟶ D,
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk c) ≫ H = F ∧
        (overPullbackUnderlying (relativeJoinBaseProjection p (𝟙 C))).map
          (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ H = G := by
  apply (kanRelativeHomDiagram_lift_iff (kanRelativeJoinInlOver p) A₀.ι c F G).2
  apply exists_kanRelativeJoin_family_extension_of_colimits p A₀ hA₀
    (kanFiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G)
    (kanFiberwiseHomCurry p c F) ?_ hcol
  erw [← kanFiberwiseHomCurry_pre (kanRelativeJoinInlOver p),
    ← kanFiberwiseHomCurry_precomp]
  exact congrArg (kanFiberwiseHomCurry p (A₀.ι ≫ c)) hFG.symm

end SerrePositivity.InfinityCategories.F1B
