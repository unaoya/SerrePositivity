module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.RelativeArrowSpecifiedRealization
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationTensor

/-!
概要：指定した両端表現の間の相対射のパラメーター族を coherent に実現する。
方針：射の族を積の底上の一本の射にし指定両端の実現定理を適用する。
規約：同じパラメーターの全単体を同時に保持する。
使われ方：写像空間全体からの復元と高次の境界固定延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対射の族をパラメーター付きの底上の射へ束ねる。
方針：元の射の族とパラメーターの第二射影を対にする。
規約：族の射はパラメーターを忘れて元の底上にある。
使われ方：パラメーター付き collage の入力。 -/
lemma relativeArrowFamily_pair_projection {E F B K : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⊗ K ⟶ F)
    (hf : f ≫ q = fst E K ≫ p) :
    lift f (snd E K) ≫ (q ▷ K) = p ▷ K := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst,
      whiskerRight_fst]
    exact hf
  · rw [Category.assoc, whiskerRight_snd, lift_snd, whiskerRight_snd]

/-- 概要：指定表現の間の任意の相対射の族を一つの coherent な区間族へ実現する。
方針：積の底上の射を collage で実現し両端の表現の積の公式を回収する。
規約：射影の次数 fiber が小さい場合。底とパラメーターの小ささは不要。
使われ方：写像空間の普遍的な族への比較の逆向きの構成。 -/
lemma exists_relativeArrowFamily_specified_coherent_realization_of_small_fibers
    {E F B K : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⊗ K ⟶ F) (hf : f ≫ q = fst E K ≫ p)
    (hp : HasSmallSimplexFibers p) (hq : HasSmallSimplexFibers q)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q) :
    ∃ (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
      (W : (Δ[1] : SSet.{u + 1}) ⊗ (E ⊗ K) ⟶ PointedSpaceInfinity.{u}),
      prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ R₀.diagram ∧
      prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ R₁.diagram ∧
      prismEndpoint 0 (E ⊗ K) ≫ W = fst E K ≫ R₀.pointedMap ∧
      prismEndpoint 1 (E ⊗ K) ≫ W = f ≫ R₁.pointedMap ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ (p ▷ K)) ≫ H := by
  obtain ⟨H, W, h₀, h₁, hw₀, hw₁, hwp⟩ :=
    exists_relativeArrow_specified_coherent_realization_of_small_fibers (p ▷ K) (q ▷ K)
      (lift f (snd E K)) (relativeArrowFamily_pair_projection p q f hf)
      (hp.tensor K) (hq.tensor K) (R₀.tensor K) (R₁.tensor K)
  refine ⟨H, W, h₀, h₁, ?_, ?_, hwp⟩
  · simpa only [LeftTransportRepresentation.tensor_pointedMap] using hw₀
  · simpa only [LeftTransportRepresentation.tensor_pointedMap, ← Category.assoc, lift_fst]
      using hw₁


/-- 概要：小さい全空間とパラメーターの実現は一般の次数 fiber の実現に従う。
方針：元の射影の次数 fiber の小ささを使う。
規約：従来の小さい族の界面を保つ。
使われ方：小さい写像空間の比較。 -/
lemma exists_relativeArrowFamily_specified_coherent_realization {E F B K : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    [∀ n, Small.{u} (K.obj n)]
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⊗ K ⟶ F) (hf : f ≫ q = fst E K ≫ p)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q) :
    ∃ (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
      (W : (Δ[1] : SSet.{u + 1}) ⊗ (E ⊗ K) ⟶ PointedSpaceInfinity.{u}),
      prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ R₀.diagram ∧
      prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ R₁.diagram ∧
      prismEndpoint 0 (E ⊗ K) ≫ W = fst E K ≫ R₀.pointedMap ∧
      prismEndpoint 1 (E ⊗ K) ≫ W = f ≫ R₁.pointedMap ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ (p ▷ K)) ≫ H := by
  exact exists_relativeArrowFamily_specified_coherent_realization_of_small_fibers p q f hf
    (hasSmallSimplexFibers_of_small_total p) (hasSmallSimplexFibers_of_small_total q) R₀ R₁

end SerrePositivity.InfinityCategories
