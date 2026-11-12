module
public import SerrePositivity.KST.ProExcision.GroupProductData

/-!
# 離散外部作用の同変性と単体的自己射の自然性

概要：定数単体的モノイドの作用の同変性を各作用元の全単体的自己射との可換性に直す。
方針：各次数の線形作用が自己準同型の nerve の自由化と同じであることを使う。
規約：KST Construction A.5、外部 G は一般のモノイドでよい。
使われ方：標準比較の自然性を外部 G 同変性へ適用する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {G T P : Type u} [Monoid G] [Group T] [Group P]
variable (ρT : G →* Monoid.End T) (ρP : G →* Monoid.End P)

/-- 概要：離散作用の各線形作用は作用自己準同型の自由化の成分。
方針：nerve の各単体への作用の定義を展開する。
規約：KST A.5。使われ方：次数ごとの同変性と全射の自然性の接続。 -/
lemma discreteNerveAction_linearized (n : SimplexCategoryᵒᵖ) (a : G) :
    linearizedSetAction (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT) n a =
      (groupLinearizedMap (ρT a)).app n := rfl

/-- 概要：離散作用に同変な実射は作用の各全単体的自己射と可換。
方針：次数ごとの同変性を自然変換の外延性で束ねる。
規約：KST A.5。使われ方：両因子の入力射と厳密化した射の自然性。 -/
lemma LinearizedEquivariant.discrete_naturality
    {f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj T)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj P))}
    (hf : LinearizedEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of P) ρP) f) (a : G) :
    groupLinearizedMap (ρT a) ≫ f = f ≫ groupLinearizedMap (ρP a) := by
  apply NatTrans.ext
  funext n
  exact hf n a

/-- 概要：離散作用に同変な実区間射は各作用元の自己射と可換。
方針：区間因子の作用を恒等として各次数の同変性を束ねる。
規約：KST A.5。使われ方：因子内の厳密化への全区間比較の自然性。 -/
lemma LinearizedCylinderEquivariant.discrete_naturality
    {h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder (nerve (SingleObj T)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj P))}
    (hh : LinearizedCylinderEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of P) ρP) h) (a : G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap (ρT a))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫ h = h ≫ groupLinearizedMap (ρP a) := by
  apply NatTrans.ext
  funext n
  exact hh n a

end SerrePositivity.KST.ProExcision
