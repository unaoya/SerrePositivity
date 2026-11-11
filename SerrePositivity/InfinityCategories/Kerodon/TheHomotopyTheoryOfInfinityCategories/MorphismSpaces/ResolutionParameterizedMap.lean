module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionRetraction

/-!
概要：旗の解像の右随伴におけるパラメーター付き写像の作用。
方針：解像からの射と、最大元の射影で引き戻したパラメーターを同時に評価する。
規約：通常の単体集合の直積を使い、𝒮 の極限は主張しない。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Corollary 5.6.0.6（Tag 028T）、高次の coherent な比較の構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：解像の右随伴にパラメーター付きの写像を作用させる。
方針：解像の単体を射へ写し、パラメーターは最大元の射影を通して評価する。
規約：入力は X⊗T→Y で、パラメーター T は同じ次数で保持する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、coherent な比較の豊穣 Hom の作用。 -/
noncomputable def coherentResolutionParameterizedMap {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X ⊗ T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Y where
  app n := ↾fun ⟨x, t⟩ ↦ ULift.up
    (lift x.down (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat.app n.unop ≫ SSet.yonedaEquiv.symm t) ≫ f)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply ULift.ext
    change lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.map α.unop ≫ x.down)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat.app m.unop ≫ SSet.yonedaEquiv.symm (T.map α t)) ≫ f =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionDiagram.map α.unop ≫
          lift x.down (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat.app n.unop ≫ SSet.yonedaEquiv.symm t) ≫ f
    rw [← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · simp only [lift_fst, Category.assoc]
    · simp only [lift_snd, Category.assoc]
      have ht : SSet.yonedaEquiv.symm (T.map α t) =
          stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm t :=
        (SSet.yonedaEquiv_symm_naturality_left α.unop t).symm
      rw [ht, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat.naturality α.unop,
        Category.assoc]

/-- 概要：パラメーターを無視する射の解像への作用は第一射影。
方針：各単体の写像を第一射影で評価し、解像からの元の射を回収する。
規約：パラメーター T は任意。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、豊穣構造の単位則の準備。 -/
lemma coherentResolutionParameterizedMap_fst (X T : SSet.{u}) :
    coherentResolutionParameterizedMap (fst X T) =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X) T := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply ULift.ext
  exact lift_fst _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
