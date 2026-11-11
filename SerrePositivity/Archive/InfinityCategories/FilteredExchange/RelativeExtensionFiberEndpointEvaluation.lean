module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation

/-!
概要：元の fiber 終点の全評価を含めると、同じ延長全族の実際の制限を回収する。
方針：元の定値相対 Hom の評価と底の等式による表示変更の式を使う。
規約：全延長と全係数を保持。使われ方：三角形比較の二つの終点表示の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の fiber 終点の全評価の包含は、元の全延長の同じ部分の評価そのもの。 -/
lemma relativeExtensionFiberEndpoint_uncurry_ι {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b) :
    uncurry (relativeExtensionFiberEndpoint p a i v hv j b hj) ≫ vertexFiberι p b =
      relativeFunctorUncurry
        (relativeFunctorExtensionSpaceι p a i v hv ≫ relativeFunctorPre p a j) := by
  unfold relativeExtensionFiberEndpoint
  change uncurry (((relativeFunctorExtensionSpaceι p a i v hv ≫ relativeFunctorPre p a j) ≫
    (eqToIso (congrArg (relativeFunctorSpace p) hj)).hom) ≫
      (relativeFunctorConstFiberIso p b).hom) ≫ _ = _
  rw [relativeConstFiberIso_uncurry, relativeFunctorUncurry_transport p hj]

end SerrePositivity.InfinityCategories.F2
