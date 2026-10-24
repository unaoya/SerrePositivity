module

public import SerrePositivity.InfinityCategories.F2.Presentable.FlipConstantFunctorHom
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipFunctorHomComposition
public import SerrePositivity.InfinityCategories.F2.Presentable.HomTransportSameEdge

/-!
概要：単位の Hom 写像を変数交換で定値 Hom の合成へ移す一般公式。
方針：交換と端点輸送の合成保存を使う。
規約：具体的な余極限の選択は入力に含めない。
使われ方：選んだ余極限単位の全 Hom 対応の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：定値後合成を続けた Hom の転置は転置した単位と定値 Hom の合成。
方針：交換と両端の輸送の合成保存を適用する。
規約：単位に随伴条件を課さない。
使われ方：具体的な余極限単位への適用。 -/
lemma flip_composite_constant_hom {A K X : SSet.{u}} [Quasicategory X]
    {U : A ⟶ (ihom K).obj X} {L V : A ⟶ X}
    (t : FunctorHom U (L ≫ constantFunctorMap K X)) (α : FunctorHom L V) :
    F1B.kanFunctorHomCongr rfl (flip_postcompose_constant V)
      (flipFunctorHomEquiv U (V ≫ constantFunctorMap K X)
        (t ≫ (hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α)) =
    F1B.kanFunctorHomCongr rfl (flip_postcompose_constant L)
      (flipFunctorHomEquiv U (L ≫ constantFunctorMap K X) t) ≫ constantFunctorHomMap K α := by
  let b : FunctorHom (L ≫ constantFunctorMap K X) (V ≫ constantFunctorMap K X) :=
    (hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α
  change F1B.kanFunctorHomCongr rfl (flip_postcompose_constant V)
    (flipFunctorHomEquiv U (V ≫ constantFunctorMap K X) (t ≫ b)) = _
  rw [flipFunctorHomEquiv_comp,
    functorHomCongr_comp rfl (flip_postcompose_constant L) (flip_postcompose_constant V)]
  exact congrArg (F1B.kanFunctorHomCongr rfl (flip_postcompose_constant L)
    (flipFunctorHomEquiv U (L ≫ constantFunctorMap K X) t) ≫ ·)
      (flip_postcompose_constant_hom (K := K) α)

/-- 概要：転置した単位の頂点表示を保って Hom の合成公式を移す。
方針：指定単位の照合と定値化の合成保存を使う。
規約：元の頂点の等式を明示する。
使われ方：native な普遍余錐から随伴の全 Hom 判定への接続。 -/
lemma flip_composite_constant_hom_of_unit {A K X : SSet.{u}} [Quasicategory X]
    {U : A ⟶ (ihom K).obj X} {L V : A ⟶ X}
    (t : FunctorHom U (L ≫ constantFunctorMap K X))
    {z : ((ihom A).obj X) _⦋0⦌}
    (τ : FunctorHom (internalHomFlipHomEquiv A K X U) (SSet.const z))
    (hz : z = functorVertex L)
    (ht : F1B.kanFunctorHomCongr rfl (flip_postcompose_constant L)
      (flipFunctorHomEquiv U (L ≫ constantFunctorMap K X) t) = τ ≫
      eqToHom (congrArg (fun z ↦ HomotopyCategory.mk
        (functorVertex (SSet.const z : K ⟶ (ihom A).obj X))) hz))
    (α : FunctorHom L V) :
    F1B.kanFunctorHomCongr rfl (flip_postcompose_constant V)
      (flipFunctorHomEquiv U (V ≫ constantFunctorMap K X)
        (t ≫ (hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α)) =
    τ ≫ constantFunctorHomMap K (eqToHom (congrArg HomotopyCategory.mk hz) ≫ α) := by
  rw [flip_composite_constant_hom, ht, constantFunctorHomMap_comp,
    constantFunctorHomMap_eqToHom K hz, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
