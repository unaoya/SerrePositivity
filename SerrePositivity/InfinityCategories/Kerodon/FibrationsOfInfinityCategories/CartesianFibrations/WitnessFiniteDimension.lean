module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessCellInduction

/-!
概要：有限次元の底上の表現空間の可縮性を低次元のセルと境界へ帰着する。
方針：空からのセル帰納法を次元の上限まで実行し全体の骨格と同定する。
規約：次元以上の標準単体に対する局所可縮性を要求しない。
使われ方：標準単体と境界の次元帰納法。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SSet.relativeCellComplexOfMono
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：次元が N 未満の単体集合の第 N 骨格は全体。
方針：全ての非退化単体が骨格に属することを示す。
規約：第 N 骨格は次元が N 未満の単体で生成する。
使われ方：有限次元のセル帰納法の終点。 -/
lemma transportSkeleton_eq_top (B : SSet.{u + 1}) (N : ℕ) [B.HasDimensionLT N] :
    B.skeleton N = ⊤ := by
  apply le_antisymm le_top
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  intro n x _
  exact B.mem_skeleton x.1 (B.dim_lt_of_nonDegenerate x N)

/-- 概要：有限次元の最終骨格は底上の恒等対象と同型。
方針：骨格が全体であることによる部分複体の同型を取る。
規約：底への包含を保つ。
使われ方：有限骨格での表現空間の可縮性を元の表現空間へ移す。 -/
def transportFiniteSkeletonIso (B : SSet.{u + 1}) (N : ℕ) [B.HasDimensionLT N] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSkeletonOver B).obj N ≅ Over.mk (𝟙 B) :=
  Over.isoMk (Subcomplex.eqToIso (transportSkeleton_eq_top B N) ≪≫ Subcomplex.topIso B) (by
    change ((Subcomplex.eqToIso (transportSkeleton_eq_top B N)).hom ≫
      (Subcomplex.topIso B).hom) ≫ 𝟙 B = (B.skeleton N).ι
    rw [Category.comp_id]
    change Subcomplex.homOfLE (transportSkeleton_eq_top B N).le ≫
      (⊤ : B.Subcomplex).ι = (B.skeleton N).ι
    exact Subcomplex.homOfLE_ι (transportSkeleton_eq_top B N).le)

/-- 概要：有限次元の底上の可縮性は次元未満の標準単体と境界の局所可縮性から従う。
方針：セルの帰納法を次元の上限まで実行し最終骨格を全体と同定する。
規約：低次元だけの局所入力を用いる。
使われ方：境界・内ホーンの可縮性を標準単体より先に証明する。 -/
lemma transportWitnessSpace_isContractibleKan_of_finiteDimension
    {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (N : ℕ) [B.HasDimensionLT N]
    (hs : ∀ n, n < N → ∀ (σ : (Δ[n] : SSet.{u + 1}) ⟶ B), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk σ))))
    (hb : ∀ n, n < N → ∀ (σ : (Δ[n] : SSet.{u + 1}) ⟶ B), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk (∂Δ[n].ι ≫ σ))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  have hsk : ∀ n, n ≤ N → _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj
      (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRelativeSkeleton (⊥ : B.Subcomplex).ι n))) := by
    intro n hn
    induction n with
    | zero =>
      have h : skeletonOfMono (⊥ : B.Subcomplex).ι 0 = ⊥ := by
        simp [skeletonOfMono_zero, Subfunctor.range_ι]
      have he := congrArg (fun T : B.Subcomplex ↦ Over.mk T.ι) h
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj
        (Opposite.op (Over.mk (skeletonOfMono (⊥ : B.Subcomplex).ι 0).ι)))
      rw [he]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessEmptyBase_isContractibleKan p
    | succ n ih =>
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessRelativeSkeletonSucc_isContractibleKan p (⊥ : B.Subcomplex).ι n
        (ih (Nat.le_of_succ_le hn)) (fun c ↦ hs n (Nat.lt_of_succ_le hn) c.map)
        (fun c ↦ hb n (Nat.lt_of_succ_le hn) c.map)
  have hN := hsk N le_rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRelativeSkeleton_empty_eq] at hN
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).mapIso
    (transportFiniteSkeletonIso B N).op).symm hN
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessIdentityPullbackIso p).symm hi

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
