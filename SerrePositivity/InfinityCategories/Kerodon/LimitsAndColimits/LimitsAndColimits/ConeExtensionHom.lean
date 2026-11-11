module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeExtensionFunctor

/-!
概要：図式を固定する拡張関手間の自然変換から錐の射を復元する。
方針：新しい始点での成分と自然性の正方形を使う。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：図式上で恒等な自然変換から元の錐の射を復元する。
方針：新しい始点で評価し自然性で錐の可換性を証明する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneMorphismOfFixedExtension {c d : Cone F}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor d)
    (h : Functor.whiskerLeft WithInitial.incl η = 𝟙 F) : c ⟶ d where
  hom := η.app WithInitial.star
  w i := by
    have hm := η.naturality (WithInitial.homTo i)
    have hi := NatTrans.congr_app h i
    change η.app (WithInitial.of i) = 𝟙 (F.obj i) at hi
    change c.π.app i ≫ η.app (WithInitial.of i) = η.app WithInitial.star ≫ d.π.app i at hm
    rw [hi, Category.comp_id] at hm
    exact hm.symm

/-- 概要：錐の射と図式上で恒等な拡張関手間の自然変換の全単射。
方針：始点での評価と成分による拡張を互いの逆にする。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneExtensionHomEquiv (c d : Cone F) : (c ⟶ d) ≃
    {η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor d //
      Functor.whiskerLeft WithInitial.incl η = 𝟙 F} where
  toFun f := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialNatTrans f, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialNatTrans_restrict f⟩
  invFun η := coneMorphismOfFixedExtension η.val η.property
  left_inv f := ConeMorphism.ext _ _ rfl
  right_inv η := by
    apply Subtype.ext
    apply NatTrans.ext
    funext x
    cases x with
    | of i => exact (NatTrans.congr_app η.property i).symm
    | star => rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
