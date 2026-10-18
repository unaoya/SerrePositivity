module

public import SerrePositivity.InfinityCategories.Core.JoinFunctor
public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：通常の join の右因子の連結な余極限の保存。
方針：固定した左因子の under 圏への join と slice の随伴を作る。
規約：既存の join の直接定義は維持する。
使われ方：Kerodon Lemma 4.6.2.10 のセルと骨格の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：左因子 K を固定した join を K の under 圏への関手にする。
方針：右包含と joinMap の自然性を使う。
規約：可変因子は右側。
使われ方：Kerodon §4.3.5・4.6.2 の slice との随伴。 -/
def joinRightUnderFunctor (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj A := Under.mk (joinInl K A)
  map {A B} f := Under.homMk (joinMap (𝟙 K) f) (by
    change joinInl K A ≫ joinMap (𝟙 K) f = joinInl K B
    rw [joinInl_joinMap, Category.id_comp])
  map_id A := by
    apply Under.UnderMorphism.ext
    exact joinMap_id K A
  map_comp f g := by
    apply Under.UnderMorphism.ext
    change joinMap (𝟙 K) (f ≫ g) = joinMap (𝟙 K) f ≫ joinMap (𝟙 K) g
    simpa only [Category.id_comp] using joinMap_comp (𝟙 K) (𝟙 K) f g

/-- 概要：K の under 圏の対象をその slice へ送る関手。
方針：各単体の錐を under 圏の射の右成分で後合成する。
規約：固定された図式の等式は under 圏の可換条件を使う。
使われ方：Kerodon §4.3.5・4.6.2 の join の余極限。 -/
def sliceUnderUnderFunctor (K : SSet.{u}) : Under K ⥤ SSet.{u} where
  obj p := sliceUnder p.hom
  map f :=
    { app n := ↾fun σ ↦ ⟨σ.val ≫ f.right, by
        rw [← Category.assoc, σ.property, Under.w]⟩
      naturality _ _ α := by
        apply ConcreteCategory.hom_ext
        intro σ
        apply Subtype.ext
        exact Category.assoc _ _ _ }
  map_id p := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.comp_id _
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm

/-- 概要：固定した左因子を持つ join と slice は under 圏を通じて随伴する。
方針：任意の単体集合に対する slice の普遍性を自然な Hom の同値にする。
規約：quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10 の join の連結な余極限の保存。 -/
def joinRightUnderAdjunction (K : SSet.{u}) : joinRightUnderFunctor K ⊣ sliceUnderUnderFunctor K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A p ↦
        { toFun f := sliceUnderCurry f.right (Under.w f)
          invFun f := Under.homMk (sliceUnderUncurry f) (sliceUnderUncurry_fixed f)
          left_inv f := by
            apply Under.UnderMorphism.ext
            exact sliceUnderUncurry_curry f.right (Under.w f)
          right_inv f := sliceUnderCurry_uncurry f }
      homEquiv_naturality_left_symm := by
        intro A B p f g
        apply Under.UnderMorphism.ext
        exact sliceUnderUncurry_precomp g f
      homEquiv_naturality_right := by
        intro A p q f g
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro a
        apply Subtype.ext
        change joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ (f.right ≫ g.right) =
          (joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ f.right) ≫ g.right
        exact (Category.assoc _ _ _).symm }

/-- 概要：under 圏への join 関手は左随伴。
方針：構成した join と slice の随伴を使う。
規約：固定した左因子 K は任意。
使われ方：Kerodon §4.6.2 の余極限保存。 -/
instance joinRightUnderFunctor_isLeftAdjoint (K : SSet.{u}) :
    (joinRightUnderFunctor K).IsLeftAdjoint := (joinRightUnderAdjunction K).isLeftAdjoint

/-- 概要：固定した左因子との通常の join は連結な余極限を保つ。
方針：左随伴の余極限保存と under 圏の忘却関手の連結な余極限保存を合成する。
規約：形 J は連結。quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10 の無限のセル分解。 -/
instance joinRightFunctor_preservesConnectedColimits (K : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] :
    PreservesColimitsOfShape J (joinRightFunctor K) := by
  change PreservesColimitsOfShape J (joinRightUnderFunctor K ⋙ Under.forget K)
  infer_instance

end SerrePositivity.InfinityCategories
