module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：標準単体を一因子とする prism とその端点の宇宙持ち上げ。
方針：標準単体の順序写像は同じものを使い、もう一つの因子と出力を ULift する。
規約：単体の添字の圏は変更しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の Kan 値図式の transport を coherent な復元の宇宙へ移す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：標準単体をパラメーターとする評価の族を宇宙持ち上げする。
方針：各次数で順序写像と入力を元の宇宙に戻し、評価の出力を持ち上げる。
規約：始域の標準単体は新しい宇宙に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、transport の prism の宇宙移送。 -/
def uliftSimplexPrism {A E : SSet.{u}} {n : ℕ} (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) :
    (Δ[n] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v, u}).obj A ⟶
      (SSet.uliftFunctor.{v, u}).obj E where
  app d := ↾fun x ↦ ULift.up (H.app d (ULift.up x.1.down, x.2.down))
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact congrArg (fun k : ((Δ[n] : SSet.{u}) ⊗ A).obj d ⟶ E.obj e ↦
      k (ULift.up x.1.down, x.2.down)) (H.naturality α)

/-- 概要：prism の宇宙持ち上げは指定頂点への制限と可換。
方針：頂点の定値単体と ULift の評価を各次数で計算する。
規約：n とその頂点 i は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げた transport の二端点の条件。 -/
lemma uliftSimplexPrism_vertex {A E : SSet.{u}} {n : ℕ}
    (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i ((SSet.uliftFunctor.{v, u}).obj A) ≫ uliftSimplexPrism.{u, v} H =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i A ≫ H) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：prism の宇宙持ち上げは全空間の射への後合成と可換。
方針：各次数で評価と後合成を計算する。
規約：標的の射 f の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げた prism の底の条件を移す準備。 -/
lemma uliftSimplexPrism_post {A E B : SSet.{u}} {n : ℕ}
    (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) (f : E ⟶ B) :
    uliftSimplexPrism.{u, v} H ≫ (SSet.uliftFunctor.{v, u}).map f =
      uliftSimplexPrism.{u, v} (H ≫ f) := rfl

/-- 概要：底の辺の定値族の prism を持ち上げると、持ち上げた辺の定値族になる。
方針：Yoneda の評価と辺の単体の ULift を計算する。
規約：追加の因子 A の値は底の族で忘れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、transport の底の辺の宇宙移送。 -/
lemma uliftSimplexPrism_edgeFamily {A B : SSet.{u}} {a b : B _⦋0⦌}
    (e : SSet.Edge a b) :
    uliftSimplexPrism.{u, v}
      (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge) =
    fst (Δ[1] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj A) ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e).edge := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
