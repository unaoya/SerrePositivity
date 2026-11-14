module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKRows

/-!
# 指定Hom図式の任意次数での前合成と逆評価

概要：斉次Homパラメータの前合成を次数ごとの加群図式で扱う。
方針：cochain合成の線形性・結合則と自由Yonedaの評価を使う。
規約：鎖射だとは仮定しない。IS-W2 B02の同じ成分照合の分割。
使われ方：HA 1.2.4、指定BK Hom比較の全パラメータでの成分照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 概要：斉次射の前合成を同じHom図式の各次数に適用する。
方針：線形合成と次数零の図式射の結合則。
規約：p+q=rを明示。使われ方：HA 1.2.4 の元の逆Yoneda評価との照合。 -/
def homDiagramDegreePrecompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r)
    (f : Homogeneous P Q p) :
    doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) q ⟶
      doubleOppositeDiagram ((homDiagramFunctor P).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) r where
  app j := ModuleCat.ofHom
    { toFun := fun z => f.comp z h
      map_add' := fun z w => Cochain.comp_add f z w h
      map_smul' := fun a z => Cochain.comp_smul f a z h }
  naturality i j a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change f.comp (z.comp (Cochain.ofHom
        (X.map ((opOpEquivalence SimplexCategory).functor.map a))) (add_zero q)) h =
      (f.comp z h).comp (Cochain.ofHom
        (X.map ((opOpEquivalence SimplexCategory).functor.map a))) (add_zero r)
    exact (Cochain.comp_assoc_of_third_is_zero_cochain f z _ h).symm

/-- 概要：同じ自由Yonedaの逆評価は斉次Homパラメータの前合成も保つ。
方針：前向き評価で検出し、既存のYoneda後合成則と元の逆射則を使う。
規約：元の標準重みの逆射。使われ方：HA 1.2.4 のBK各行の合成の計算。 -/
theorem freeUnitWeightEnd_inv_degree_precompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r)
    (f : Homogeneous P Q p) (n : ℕ) (z : Homogeneous Q (X.obj ⦋n⦌) q) :
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))).inv.f q z ≫
      homDiagramDegreePrecompose X p q r h f =
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).inv.f r (f.comp z h) := by
  let eP := (freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
    (doubleOppositeDiagram ((homDiagramFunctor P).obj X))
  let eQ := (freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
    (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun t => HomologicalComplex.Hom.f t r) eP.inv_hom_id) (f.comp z h)
  have hq := ConcreteCategory.congr_hom
    (congrArg (fun t => HomologicalComplex.Hom.f t q) eQ.inv_hom_id) z
  change eP.hom.f r (eP.inv.f r (f.comp z h)) = f.comp z h at hp
  change eQ.hom.f q (eQ.inv.f q z) = z at hq
  apply (ModuleCat.mono_iff_injective (eP.hom.f r)).mp inferInstance
  rw [hp]
  change ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).hom.app
    (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).f r _ = _
  rw [freeUnitWeightEndNatIso_hom_f_apply, freePresheafHomLinearEquiv_comp]
  change f.comp
    ((freePresheafHomLinearEquiv (R := A) (ModuleCat.of A A) (Opposite.op ⦋n⦌)
      (doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) q) (eQ.inv.f q z)) (1 : A)) h =
    f.comp z h
  change ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).hom.app
    (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))).f q (eQ.inv.f q z) = z at hq
  rw [freeUnitWeightEndNatIso_hom_f_apply] at hq
  rw [hq]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
