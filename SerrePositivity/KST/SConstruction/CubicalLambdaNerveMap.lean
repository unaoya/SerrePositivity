module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerve

/-! # 元の Λ 実 dg 関手 nerve の厳密 dg 後合成
概要：元の全実 dg 関手の単体集合へ厳密 dg 関手を後合成し、恒等・合成を保つ。
方針：元の実 dg 合成の結合則を全対象と全 Hom で照合する。
規約：共通の対象宇宙と元の全退化を保持。使われ方：native dg nerve 比較の入力自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D E T : Type v}
  [DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- 元の Λ 実 dg 関手 nerve への、元の厳密 dg 後合成による実単体的写像。 -/
def cubicalLambdaNerveMap (F : DGFunctor A D E) :
    cubicalLambdaNerve A D ⟶ cubicalLambdaNerve A E where
  app _ := ↾fun G => DGFunctor.comp G F
  naturality X Y f := by
    ext G
    refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
    intro x y
    exact (Category.comp_id _).trans (Category.assoc _ _ _)

/-- 元の後合成の全単体での作用は、元の同じ実 dg 合成そのもの。 -/
lemma cubicalLambdaNerveMap_app {N : ℕ} (F : DGFunctor A D E)
    (G : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) :
    (cubicalLambdaNerveMap A F).app (op ⦋N⦌) G = DGFunctor.comp G F := rfl

/-- 元の厳密 dg 恒等関手の後合成は、元の全実 dg 関手 nerve の恒等写像。 -/
lemma cubicalLambdaNerveMap_id : cubicalLambdaNerveMap A (DGFunctor.id D) =
    𝟙 (cubicalLambdaNerve A D) := by
  ext n G
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.comp_id _)

/-- 元の厳密 dg 合成の後合成は、元の全実 dg 関手 nerve の写像合成を厳密に保つ。 -/
lemma cubicalLambdaNerveMap_comp (F : DGFunctor A D E) (G : DGFunctor A E T) :
    cubicalLambdaNerveMap A (DGFunctor.comp F G) =
      cubicalLambdaNerveMap A F ≫ cubicalLambdaNerveMap A G := by
  ext n H
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
