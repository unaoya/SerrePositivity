module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.HomSquareBijective
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionFullFaithfulness
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitConstantFamily

/-!
概要：定値族の Hom 制限の全単射から指定した二関手間の写像空間の制限を判定する。
方針：内部 Hom の交換同型で定値族を転置し、全パラメータの Hom 判定へ渡す。
規約：他の関手対に対する充満忠実性を仮定しない。
使われ方：標準左 Kan 関手から出る元の制限の pinched 写像の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：転置後の定値族の Hom 全単射は元の定値関手間の Hom 全単射を与える。
方針：内部 Hom の交換の自然な正方形で Hom 全単射を移し、後合成の端点同型を補う。
規約：指定した F・G の対だけを検査する。
使われ方：区間写像空間の全パラメータ判定への入力。 -/
lemma constantHomPrecomposition_bijective_of_transpose {A K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (F G : C ⟶ D)
    (h : Function.Bijective
      ((hoFunctor.map ((pre δ).app ((ihom A).obj D))).toFunctor.map :
        FunctorHom (F ≫ constantFunctorMap A D) (G ≫ constantFunctorMap A D) → _)) :
    Function.Bijective
      (SerrePositivity.InfinityCategories.F1B.constantHomPostcomp ((pre δ).app D) A (functorVertex F) (functorVertex G)) := by
  let P := (hoFunctor.map ((ihom A).map ((pre δ).app D))).toFunctor
  let Q := (hoFunctor.map ((pre δ).app ((ihom A).obj D))).toFunctor
  let L := (hoFunctor.map (internalHomSwapIso A C D).hom).toFunctor
  let M := (hoFunctor.map (internalHomSwapIso A K D).hom).toFunctor
  let x := HomotopyCategory.mk (functorVertex (SSet.const (functorVertex F) :
    A ⟶ (ihom C).obj D))
  let y := HomotopyCategory.mk (functorVertex (SSet.const (functorVertex G) :
    A ⟶ (ihom C).obj D))
  have he : P ⋙ M = L ⋙ Q := by
    dsimp only [P, Q, L, M]
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      internalHomSwapIso_pre, CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor]
  have hQ : Function.Bijective (Q.map : (L.obj x ⟶ L.obj y) → _) := by
    change Function.Bijective (Q.map :
      FunctorHom (SerrePositivity.InfinityCategories.F1B.functorTranspose (SSet.const (functorVertex F) : A ⟶ (ihom C).obj D))
        (SerrePositivity.InfinityCategories.F1B.functorTranspose (SSet.const (functorVertex G) : A ⟶ (ihom C).obj D)) → _)
    rw [kanFunctorTranspose_const, kanFunctorTranspose_const]
    exact h
  have hb := SerrePositivity.InfinityCategories.F1B.homMap_bijective_of_iso_square P Q L M
    (qCatEquivalenceOfIso (internalHomSwapIso A C D)).isFullyFaithful.toHoFullyFaithful
    (qCatEquivalenceOfIso (internalHomSwapIso A K D)).isFullyFaithful.toHoFullyFaithful
    (eqToIso he) x y hQ
  let e : ConstantFunctorHom A ((ihom C).obj D) (functorVertex F) (functorVertex G) ≃
      FunctorHom ((SSet.const (functorVertex F) : A ⟶ (ihom C).obj D) ≫ (pre δ).app D)
        ((SSet.const (functorVertex G) : A ⟶ (ihom C).obj D) ≫ (pre δ).app D) :=
    Equiv.ofBijective _ hb
  exact (e.trans ((constantFunctorCompIso A (functorVertex F) ((pre δ).app D)).homCongr
    (constantFunctorCompIso A (functorVertex G) ((pre δ).app D)))).bijective

/-- 概要：全パラメータの転置後の Hom 全単射から指定 pinched 制限の同値を得る。
方針：元の定値関手間の Hom 全単射へ移して、実際の区間比較の逆を構成する判定を使う。
規約：F・G の間の指定された pinchedHomMap 自身のホモトピー同値。
使われ方：元の Kan 関手から出る写像空間の制限定理。 -/
lemma precomposition_pinchedHomMap_equivalence_of_constantFamily {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (F G : C ⟶ D)
    (h : ∀ A : SSet.{u}, Function.Bijective
      ((hoFunctor.map ((pre δ).app ((ihom A).obj D))).toFunctor.map :
        FunctorHom (F ≫ constantFunctorMap A D) (G ≫ constantFunctorMap A D) → _)) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap ((pre δ).app D) (functorVertex F) (functorVertex G)) := by
  apply SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_constantHom_bijective
  intro A _
  exact constantHomPrecomposition_bijective_of_transpose δ F G (h A)

end SerrePositivity.InfinityCategories.F1B
