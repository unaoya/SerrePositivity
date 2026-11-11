module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation

/-!
概要：実終点の底変換の逆を含めた表示を、元の全延長の同じ制限へ戻す。
方針：相対 uncurry の底変換の式と引き戻しの第一射影で底の輸送を除く。
規約：全延長と全パラメータを保持。使われ方：同じ prism の二つの fiber 出力の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 実終点を展開して pointed 成分を取ると、元の延長全族の同じ部分への制限になる。 -/
lemma relativeFunctorExtensionEndpoint_uncurry_fst {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q) :
    relativeFunctorUncurry (relativeFunctorExtensionEndpoint p b i v hv j q a hj) ≫
      pullback.fst p q =
      relativeFunctorUncurry
        (relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPre p b j) := by
  unfold relativeFunctorExtensionEndpoint
  simp only [← Category.assoc]
  change relativeFunctorUncurry
    (((relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPre p b j) ≫
      eqToHom (congrArg (relativeFunctorSpace p) hj)) ≫
        relativeFunctorBaseChangeBackward p q a) ≫ pullback.fst p q = _
  rw [relativeFunctorBaseChangeBackward_uncurry, pullback.lift_fst]
  exact relativeFunctorUncurry_transport p hj _

end SerrePositivity.InfinityCategories.F2
