module
public import SerrePositivity.KST.SConstruction.FunctorInitialBoundary
public import SerrePositivity.KST.SConstruction.InitialBoundaryIso
public import SerrePositivity.InfinityCategories.Stable.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Stable.PushoutShape
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap

/-! # 関手 ∞ 圏の点ごとの余極限
概要：各点で余極限となる余錐は関手 ∞ 圏でも余極限となる。
方針：A6 の二重内部 Hom の交換と相対始点境界充填を合わせる。
規約：Core の公開 API を変えずに余極限側を構成する。
使われ方：HTT 5.1.2.2、gapped 図式の点ごとの押し出し。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：関手圏の余錐を指定した頂点で評価する。
方針：内部 Hom の評価で余錐とその図式を同時に後合成する。
規約：添字とパラメーターは任意。使われ方：点ごとの余極限の定義。 -/
def evaluateFunctorCocone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) (k : K _⦋0⦌) : JoinCocone (evaluateFunctorDiagram p k) :=
  ⟨c.val ≫ evaluateFunctorAt k, by rw [← Category.assoc, c.property]; rfl⟩

/-- 概要：全ての評価した余錐が余極限となる条件。
方針：各頂点で通常の IsColimitCone を要求する。
規約：関手圏の余極限との比較を定義に含めない。使われ方：HTT 5.1.2.2 の余極限側。 -/
def IsPointwiseColimitCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCocone p) : Prop := ∀ k : K _⦋0⦌, IsColimitCone (evaluateFunctorCocone c k)

/-- 概要：評価した余錐の相対始点境界充填は関手圏の余錐の相対始点境界充填を与える。
方針：内部 Hom の二つの始域を交換し、点ごとの充填を移送する。
規約：点ごとの仮定は余極限性より強い相対充填として明記する。
使われ方：Kerodon Proposition 7.1.8.10 の空図式への還元。 -/
lemma initialBoundaryLifting_coconeRestriction_of_pointwise {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p)
    (hc : ∀ k : K _⦋0⦌, InitialBoundaryLifting (coconeRestriction J X)
      (functorVertex (evaluateFunctorCocone c k).val)) :
    InitialBoundaryLifting (coconeRestriction J ((ihom K).obj X)) (functorVertex c.val) := by
  let T := join J (Δ[0] : SSet.{u})
  let f : K ⟶ (ihom T).obj X := curry ((β_ T K).hom ≫ uncurry c.val)
  have hs : (internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (functorVertex f) =
      functorVertex c.val := by
    rw [internalHomSwapIso_functorVertex]
    dsimp [f]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_uncurry]
  have hf : ∀ k : K _⦋0⦌, f.app (Opposite.op ⦋0⦌) k =
      functorVertex (evaluateFunctorCocone c k).val := by
    intro k
    have he := congrArg
      (fun q : (ihom K).obj ((ihom T).obj X) ⟶ (ihom T).obj X ↦
        q.app (Opposite.op ⦋0⦌) (functorVertex f)) (internalHomSwapIso_evaluate K T X k)
    change ((ihom T).map (evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
        ((internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (functorVertex f)) =
      (evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (functorVertex f) at he
    rw [hs, evaluateFunctorAt_functorVertex] at he
    exact he.symm
  have ht : InitialBoundaryLifting ((ihom K).map (coconeRestriction J X)) (functorVertex f) :=
    initialBoundaryLifting_ihom_of_pointwise (coconeRestriction J X) f (by
      intro k
      rw [hf]
      exact hc k)
  have hq : (internalHomSwapIso K T X).hom ≫ coconeRestriction J ((ihom K).obj X) =
      (ihom K).map (coconeRestriction J X) ≫ (internalHomSwapIso K J X).hom :=
    (internalHomSwapIso_pre (A := K) (X := X) (joinInl J Δ[0])).symm
  have h := initialBoundaryLifting_map_iso (internalHomSwapIso K T X) (internalHomSwapIso K J X) hq ht
  rwa [hs] at h

/-- 概要：評価した余錐が余錐の制限に対する相対始点境界充填を満たせば関手圏の余極限余錐となる。
方針：点ごとの相対充填を関手圏へ移し、fiber の始対象性で判定する。
規約：X は quasicategory。点ごとの余極限性だけからの結論はまだ含めない。
使われ方：HTT 5.1.2.2 の相対境界判定から余極限への接続。 -/
lemma isColimitCone_of_pointwise_initialBoundaryLifting {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p)
    (hc : ∀ k : K _⦋0⦌, InitialBoundaryLifting (coconeRestriction J X)
      (functorVertex (evaluateFunctorCocone c k).val)) : IsColimitCone c :=
  isColimitCone_of_initialBoundaryLifting_coconeRestriction c
    (initialBoundaryLifting_coconeRestriction_of_pointwise c hc)


/-- 概要：点ごとに余極限である関手圏の余錐は余極限。
方針：各点の余極限性を相対始点境界充填に変え、内部 Hom の交換で移す。
規約：X は quasicategory。添字 J とパラメーター K は任意。
使われ方：HTT 5.1.2.2 と cofiber 族の普遍性。 -/
lemma isColimitCone_of_pointwise {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p) (hc : IsPointwiseColimitCone c) :
    IsColimitCone c := by
  apply isColimitCone_of_pointwise_initialBoundaryLifting c
  intro k
  exact (hc k).initialBoundaryLifting

/-- 概要：関手圏の四角形が全ての点で押し出しなら関手圏でも押し出し。
方針：span の余錐の点ごとの余極限判定を適用する。
規約：X は quasicategory、K は任意。使われ方：Ar 上の cofiber の族の押し出し。 -/
lemma isPushoutSquare_of_pointwise {K X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj X)
    (hF : ∀ k : K _⦋0⦌, IsPushoutSquare (F ≫ evaluateFunctorAt k)) : IsPushoutSquare F := by
  apply isColimitCone_of_pointwise (pushoutCocone F)
  intro k
  exact hF k

end SerrePositivity.KST.SConstruction
