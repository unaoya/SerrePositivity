module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightUnitEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CurryFirstPrecomposition

/-!
概要：端点正規化付き後合成による同じcurry射の点評価。
方針：既存の正規化した射作用とcurryの点評価の法則を合成する。
規約：元の射を保ち、充填条件を追加しない。
使われ方：Kerodon §5.6（Tag 027M）の分類の係数移送と、指定Yoneda単位の点評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：正規化した後合成の値は同じ射作用と端点移送だけ異なる。
方針：既存の正規化の法則を使う。規約：元の値。
使われ方：同じ射の評価の計算。 -/
lemma postcomposeFunctorHom_value_heq {A X Y : SSet.{u}} (q : X ⟶ Y)
    {F G : A ⟶ X} (α : FunctorHom F G) :
    HEq (postcomposeFunctorHom q α)
      ((hoFunctor.map ((ihom A).map q)).toFunctor.map α) :=
  normalizedVertexHomMap_heq ((ihom A).map q) rfl rfl α

/-- 概要：端点を保つ同じ射の二表示は正規化した後合成でも一致する。
方針：端点等式と同じ射の等式を消去する。
規約：同じ後合成関手。使われ方：指定単位の表示変更後の評価。 -/
lemma postcomposeFunctorHom_heq_of_heq {A X Y : SSet.{u}} (q : X ⟶ Y)
    {F G F' G' : A ⟶ X} (hF : F = F') (hG : G = G')
    (α : FunctorHom F G) (β : FunctorHom F' G') (h : HEq α β) :
    HEq (postcomposeFunctorHom q α) (postcomposeFunctorHom q β) := by
  subst F' G'
  cases eq_of_heq h
  rfl

/-- 概要：同じcurry射を正規化付きで点評価すると元の固定変数制限になる。
方針：正規化した後合成の値と既存のcurry評価の法則をつなぐ。
規約：全図式の同じ射。使われ方：指定単位の係数移送。 -/
lemma curryFunctorHom_postcompose_evaluate_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} (α : FunctorHom f g) (a : A _⦋0⦌) :
    HEq (postcomposeFunctorHom (evaluateFunctorAt (Y := X) a) (curryFunctorHom α))
      (precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) α) :=
  (postcomposeFunctorHom_value_heq (evaluateFunctorAt (Y := X) a) (curryFunctorHom α)).trans
    (curryFunctorHom_evaluate_heq α a)

/-- 概要：同じcurry射の端点表示を移してからの正規化付き評価も元の固定変数制限。
方針：同じ後合成の表示変更則と一般評価則を合成する。
規約：入力の射自身の一致を使う。使われ方：元の指定Yoneda単位の評価。 -/
lemma curryFunctorHom_postcompose_evaluate_of_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} {f' g' : B ⟶ (ihom A).obj X}
    (α : FunctorHom f g) (β : FunctorHom f' g')
    (hf : f' = curry f) (hg : g' = curry g) (h : HEq β (curryFunctorHom α))
    (a : A _⦋0⦌) :
    HEq (postcomposeFunctorHom (evaluateFunctorAt (Y := X) a) β)
      (precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) α) :=
  (postcomposeFunctorHom_heq_of_heq (evaluateFunctorAt (Y := X) a) hf hg β
    (curryFunctorHom α) h).trans (curryFunctorHom_postcompose_evaluate_heq α a)

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
