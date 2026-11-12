module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorRestrictedEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：底の表示変更と引き戻しを含む相対端点評価の展開を、元の実制限へ同定する。
方針：相対底変換の逆射を展開し、表示変更を消去する。
規約：任意の全パラメータ。使われ方：始点も動く prism 空間の切断と作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 指定端点評価の pointed 成分は、元の全族の同じ端点での実制限。 -/
lemma relativeFunctorRestrictedEndpoint_uncurry {A C E F B T : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
    (hj : j ≫ b = a ≫ q) (k : T ⟶ relativeFunctorSpace p b) :
    relativeFunctorUncurry (k ≫ relativeFunctorRestrictedEndpoint p b j q a hj) ≫
      pullback.fst p q = (j ▷ T) ≫ relativeFunctorUncurry k := by
  unfold relativeFunctorRestrictedEndpoint
  rw [← Category.assoc k, ← Category.assoc (k ≫ relativeFunctorPre p b j)]
  change relativeFunctorUncurry
    (((k ≫ relativeFunctorPre p b j) ≫ eqToHom (congrArg (relativeFunctorSpace p) hj)) ≫
      relativeFunctorBaseChangeBackward p q a) ≫ pullback.fst p q = _
  rw [relativeFunctorBaseChangeBackward_uncurry, pullback.lift_fst]
  change relativeFunctorUncurry
    ((k ≫ relativeFunctorPre p b j) ≫ (eqToIso (congrArg (relativeFunctorSpace p) hj)).hom) = _
  rw [relativeFunctorUncurry_transport p hj, relativeFunctorUncurry_pre]

end SerrePositivity.InfinityCategories.F2
