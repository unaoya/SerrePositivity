module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import Mathlib.Tactic.CrossRefAttribute

/-! # 関手 ∞ 圏の点ごとの余極限
概要：各点で余極限となる余錐は関手 ∞ 圏でも余極限となる。
方針：A6 の二重内部 Hom の交換と相対始点境界充填を合わせる。
規約：Core の公開 API を変えずに余極限側を構成する。
使われ方：HTT 5.1.2.2、gapped 図式の点ごとの押し出し。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：関手圏の余錐を指定した頂点で評価する。
方針：内部 Hom の評価で余錐とその図式を同時に後合成する。
規約：添字とパラメーターは任意。使われ方：点ごとの余極限の定義。 -/
def evaluateFunctorCocone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (k : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram p k) :=
  ⟨c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k, by rw [← Category.assoc, c.property]; rfl⟩

/-- 概要：全ての評価した余錐が余極限となる条件。
方針：各頂点で通常の IsColimitCone を要求する。
規約：関手圏の余極限との比較を定義に含めない。使われ方：HTT 5.1.2.2 の余極限側。 -/
@[kerodon 05QF]
def IsPointwiseColimitCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : Prop := ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (evaluateFunctorCocone c k)

/-- 概要：評価した余錐の相対始点境界充填は関手圏の余錐の相対始点境界充填を与える。
方針：内部 Hom の二つの始域を交換し、点ごとの充填を移送する。
規約：点ごとの仮定は余極限性より強い相対充填として明記する。
使われ方：Kerodon Proposition 7.1.8.10（Tag 02XK） の空図式への還元。 -/
lemma initialBoundaryLifting_coconeRestriction_of_pointwise {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (evaluateFunctorCocone c k).val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J ((ihom K).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})
  let f : K ⟶ (ihom T).obj X := curry ((β_ T K).hom ≫ uncurry c.val)
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex]
    dsimp [f]
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
      curry_uncurry]
  have hf : ∀ k : K _⦋0⦌, f.app (Opposite.op ⦋0⦌) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (evaluateFunctorCocone c k).val := by
    intro k
    have he := congrArg
      (fun q : (ihom K).obj ((ihom T).obj X) ⟶ (ihom T).obj X ↦
        q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate K T X k)
    change ((ihom T).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) at he
    rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at he
    exact he.symm
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) :=
    initialBoundaryLifting_ihom_of_pointwise (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X) f (by
      intro k
      rw [hf]
      exact hc k)
  have hq : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J ((ihom K).obj X) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K J X).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre (A := K) (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0])).symm
  have h := initialBoundaryLifting_map_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K T X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K J X) hq ht
  rwa [hs] at h

/-- 概要：評価した余錐が余錐の制限に対する相対始点境界充填を満たせば関手圏の余極限余錐となる。
方針：点ごとの相対充填を関手圏へ移し、fiber の始対象性で判定する。
規約：X は quasicategory。点ごとの余極限性だけからの結論はまだ含めない。
使われ方：HTT 5.1.2.2 の相対境界判定から余極限への接続。 -/
lemma isColimitCone_of_pointwise_initialBoundaryLifting {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (evaluateFunctorCocone c k).val)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction c
    (initialBoundaryLifting_coconeRestriction_of_pointwise c hc)


/-- 概要：点ごとに余極限である関手圏の余錐は余極限。
方針：各点の余極限性を相対始点境界充填に変え、内部 Hom の交換で移す。
規約：X は quasicategory。添字 J とパラメーター K は任意。
使われ方：HTT 5.1.2.2 と cofiber 族の普遍性。 -/
@[kerodon 02XP]
lemma isColimitCone_of_pointwise {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply isColimitCone_of_pointwise_initialBoundaryLifting c
  intro k
  exact (hc k).initialBoundaryLifting

/-- 概要：関手圏の四角形が全ての点で押し出しなら関手圏でも押し出し。
方針：span の余錐の点ごとの余極限判定を適用する。
規約：X は quasicategory、K は任意。使われ方：Ar 上の cofiber の族の押し出し。 -/
lemma isPushoutSquare_of_pointwise {K X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj X)
    (hF : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  apply isColimitCone_of_pointwise (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)
  intro k
  exact hF k

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
