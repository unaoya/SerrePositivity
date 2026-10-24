module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeHomDiagramOverLiftingEquiv
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRelativeFamilyAssembly

/-!
概要：変動する添字の局所相対余錐から標的の全図式を固定した実際の延長を組み立てる。
方針：図式を族へ curry し、相対骨格で延長した族を三つの条件を保って戻す。
規約：標的の射は単射による関手の制限。
使われ方：境界固定の関手圏における相対 Kan 拡張の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所の相対余錐条件から部分図式と標的の全図式を同時に保つ延長が存在する。
方針：curry の前後合成の自然性で族の持ち上げ問題を作り、相対的な組み立てを適用する。
規約：欠けた正次元単体の最初の頂点の局所相対普遍性だけを要求する。
使われ方：相対 Kan の写像空間の制限定理に必要な変動する局所形の延長。 -/
lemma exists_kanRelativeJoin_relativeDiagram_extension {K C P Q X A : SSet.{u}}
    [Quasicategory C] [Quasicategory X] (p : K ⟶ C) [CocartesianFibration p]
    (v : P ⟶ Q) [Mono v] (c : A ⟶ C) (A₀ : A.Subcomplex)
    (hA₀ : ∀ x : A _⦋0⦌, x ∈ A₀.obj (Opposite.op ⦋0⦌))
    (F : pullback c p ⟶ (ihom Q).obj X)
    (G : pullback (A₀.ι ≫ c) (relativeJoinBaseProjection p (𝟙 C)) ⟶ (ihom Q).obj X)
    (H₀ : pullback c (relativeJoinBaseProjection p (𝟙 C)) ⟶ (ihom P).obj X)
    (hFG : (overPullbackUnderlying p).map
      (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ F =
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk (A₀.ι ≫ c)) ≫ G)
    (hFU : F ≫ (pre v).app X = overPullbackMap (kanRelativeJoinInlOver p) (Over.mk c) ≫ H₀)
    (hGU : G ≫ (pre v).app X =
      (overPullbackUnderlying (relativeJoinBaseProjection p (𝟙 C))).map
        (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ H₀)
    (hlocal : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      ∃ (b : C _⦋0⦌) (d : vertexFiber p b ⟶ (ihom Q).obj X) (z : JoinCocone d),
        KanRelativeCoconeLifting ((pre v).app X) z ∧
        (((kanRelativeJoinCoconeFiberIso p b ((ihom Q).obj X)).hom.app (Opposite.op ⦋0⦌)
          (functorVertex z.val)).val) =
          (SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G).app
            (Opposite.op ⦋0⦌) ⟨simplexFirstVertex σ, hA₀ _⟩) :
    ∃ H : pullback c (relativeJoinBaseProjection p (𝟙 C)) ⟶ (ihom Q).obj X,
      overPullbackMap (kanRelativeJoinInlOver p) (Over.mk c) ≫ H = F ∧
        (overPullbackUnderlying (relativeJoinBaseProjection p (𝟙 C))).map
          (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ H = G ∧
        H ≫ (pre v).app X = H₀ := by
  apply (kanRelativeHomDiagram_lift_iff_over (kanRelativeJoinInlOver p) A₀.ι c
    ((pre v).app X) F G H₀).2
  apply exists_kanRelativeJoin_relativeFamily_extension p v A₀ hA₀
    (SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G)
    (SerrePositivity.InfinityCategories.fiberwiseHomCurry p c F)
    (SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) c H₀) ?_ ?_ ?_ hlocal
  · exact (SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp p ((pre v).app X) c F).symm.trans
      ((congrArg (SerrePositivity.InfinityCategories.fiberwiseHomCurry p c) hFU).trans
        (kanFiberwiseHomCurry_pre (kanRelativeJoinInlOver p) c H₀))
  · exact (kanFiberwiseHomCurry_pre (kanRelativeJoinInlOver p) (A₀.ι ≫ c) G).symm.trans
      ((congrArg (SerrePositivity.InfinityCategories.fiberwiseHomCurry p (A₀.ι ≫ c)) hFG.symm).trans
        (SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp p A₀.ι c F))
  · calc
      SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c) G ≫
          SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) ((pre v).app X) =
        SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c)
          (G ≫ (pre v).app X) := (SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp _ _ _ G).symm
      _ = SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c)
          ((overPullbackUnderlying (relativeJoinBaseProjection p (𝟙 C))).map
            (Over.homMk A₀.ι rfl : Over.mk (A₀.ι ≫ c) ⟶ Over.mk c) ≫ H₀) := congrArg
              (SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) (A₀.ι ≫ c)) hGU
      _ = A₀.ι ≫ SerrePositivity.InfinityCategories.fiberwiseHomCurry (relativeJoinBaseProjection p (𝟙 C)) c H₀ :=
        SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp (relativeJoinBaseProjection p (𝟙 C)) A₀.ι c H₀

end SerrePositivity.InfinityCategories.F1B
