module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphRightUnit
public import SerrePositivity.DifferentialGraded.Complexes.CurryingNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorGeneratorMaps

/-! # 元の graph 合成射と dg 関手の Hom 作用
概要：元の graph 合成射を coend 包含上の左作用として計算する。
方針：全 Hom end の Yoneda 評価と逆転置を使い、Hom 射を明示的に保持する。
規約：元の graph 比較を変更しない。使われ方：三重 graph 合成の結合則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (E : Type v) (T : Type w)
  [DGCategory A E] [DGCategory A T] [Small.{u} T]

/-- graph の左加群の Hom 射は、元の dg Hom 作用と Yoneda end 評価の合成。 -/
lemma dgFunctorGraph_leftAt_map (G : DGFunctor A E T) (t : T) (x y : E) :
    ((functorGraph A E T G).leftAt t).map x y =
      G.map x y ≫ yonedaHom A T (G.obj x) (G.obj y) ≫
        moduleHomπ A T (representable A (G.obj x)) (representable A (G.obj y)) t := by
  change (G.map x y ≫ yonedaHom A T (G.obj x) (G.obj y)) ≫
    moduleHomπ A T (representable A (G.obj x)) (representable A (G.obj y)) t = _
  exact Category.assoc _ _ _

/-- 元の dg Yoneda の評価作用は、代表右加群の同じ作用射である。 -/
lemma dgYoneda_action_chain (x y t : T) :
    uncurryRight (yonedaHom A T x y ≫
      moduleHomπ A T (representable A x) (representable A y) t) =
      BalancedTensor.rightAction A T (representable A y) t x := by
  apply tensorHom_ext
  intro p r n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro h
  change (uncurryRight (yonedaHom A T x y ≫
    moduleHomπ A T (representable A x) (representable A y) t)).f n
      (ιTensorObj (x ⟶[Complex A] y) (t ⟶[Complex A] x) p r n hn (f ⊗ₜ[A] h)) =
    (BalancedTensor.rightAction A T (representable A y) t x).f n
      (ιTensorObj (x ⟶[Complex A] y) (t ⟶[Complex A] x) p r n hn (f ⊗ₜ[A] h))
  rw [uncurryRight_apply, BalancedTensor.rightAction_apply]
  change (((moduleHomπ A T (representable A x) (representable A y) t).f p
    ((yonedaHom A T x y).f p f)).v r n (by omega)) h =
      (p * r).negOnePow • forward A h f (by omega)
  exact yonedaHom_element A T x y t f h (by omega)

/-- graph の左作用は、元の Hom 作用を代表加群の作用へ渡す射。 -/
lemma dgFunctorGraph_leftAction_chain (G : DGFunctor A E T) (t : T) (x y : E) :
    BalancedTensor.leftAction A E ((functorGraph A E T G).leftAt t) x y =
      (G.map x y ▷ (t ⟶[Complex A] G.obj x)) ≫
        BalancedTensor.rightAction A T (representable A (G.obj y)) t (G.obj x) := by
  dsimp only [BalancedTensor.leftAction]
  rw [dgFunctorGraph_leftAt_map, uncurryRight_precompose, dgYoneda_action_chain]
  rfl

section Composition
variable (D : Type z) [DGCategory A D] [Small.{u} E]

/-- 元の graph 合成射は各 coend 包含上で、同じ graph 左作用を回収する。 -/
lemma dgFunctorGraphComposition_iota (F : DGFunctor A D E) (G : DGFunctor A E T)
    (t : T) (d : D) (e : E) :
    BalancedTensor.ι A E ((functorGraph A D E F).rightAt d)
        ((functorGraph A E T G).leftAt t) e ≫
        (BimoduleCategory.valueEvaluation A T D t d).map
          (dgFunctorGraphCompositionIso A D E T F G).hom =
      BalancedTensor.leftAction A E ((functorGraph A E T G).leftAt t) e (F.obj d) := by
  rw [dgFunctorGraphCompositionIso_hom_value]
  exact BalancedTensor.ι_yonedaEvaluation A E (F.obj d)
    ((functorGraph A E T G).leftAt t) e

end Composition
end SerrePositivity.KST.SConstruction
