module

public import SerrePositivity.KST.Spectra.FreeActionFamilyEquiv
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import Mathlib.CategoryTheory.Yoneda

/-!
概要：自由 G 集合の重みを持つ同変 end と通常の内部 Hom の同型。
方針：パラメーター付き同変族の同値を curry し、Yoneda の充満忠実性で表現対象を比較する。
規約：同型は任意の係数の作用について実際に構成する。
使われ方：Goerss–Jardine VIII §2。群作用の余単体 cochain 各値の Kan 性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet Opposite
open scoped MonoidalClosed


namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G] (S : Type u) (B : Action SSet.{u} G)

/-- 概要：自由作用の end への射は通常の内部 Hom への射と同値。
方針：end の普遍性、自由軌道への制限、閉構造の随伴を合成する。
規約：パラメーターは任意の単体集合。
使われ方：Goerss–Jardine VIII §2。end の表現対象の比較。 -/
def homEquiv (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) ≃
      (A ⟶ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj B.V) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv (weight S) (coefficients B) A).trans
    ((equiv S B A).trans
      ((ihom.adjunction ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).homEquiv A B.V))

lemma homEquiv_apply {A : SSet.{u}}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) :
    homEquiv S B A f = curry (restrict S B (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f)) := rfl

/-- 概要：自由作用の end の Hom の同値はパラメーターに自然。
方針：end の uncurry と自由軌道への制限と curry の各前合成の公式を使う。
規約：厳密な射の等式。
使われ方：Goerss–Jardine VIII §2。Yoneda による内部 Hom の同型。 -/
lemma homEquiv_pre {A A' : SSet.{u}} (f : A ⟶ A')
    (s : A' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) :
    homEquiv S B A (f ≫ s) = f ≫ homEquiv S B A' s := by
  rw [homEquiv_apply, homEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp,
    restrict_pre, curry_natural_left]

/-- 概要：自由 G 集合の同変 end は軌道集合からの通常の内部 Hom と同型。
方針：全てのパラメーターの Hom の自然な同値を Yoneda で戻す。
規約：G の有限性や係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。群作用の cochain の各次数の関数空間の表示。 -/
def endIso : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B) ≅
    (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj B.V :=
  Yoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun A ↦ (homEquiv S B A.unop).toIso) (fun {A A'} f ↦ by
      ext s
      exact homEquiv_pre S B f.unop s))

end

end SerrePositivity.KST.Spectra.FreeActionFamily
