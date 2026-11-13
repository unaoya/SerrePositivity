module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramIso
/-!
概要：指定自由重み比較を図式の評価へ戻した実射を計算する。
方針：指定成分交換の単位・余単位を打ち消し、元の零延長とMoore比較を残す。
規約：IS-W2 B02の同じ係数移送の証明分割。A12の比較の順射を変えない。
使われ方：HA 1.2.4、元の線形重みHomと同じ自由鎖随伴の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
/-- 指定自由重み比較を評価へ戻すと、元の零延長・Moore比較と交換単位になる。 -/
theorem freeLinearWeightDiagramIso_hom_evaluation (W : J ⥤ SSet.{0}) :
    complexOfFunctorsToFunctorToComplex.map (freeLinearWeightDiagramIso A W).hom =
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).hom.app
        ((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)) ≫
      Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).hom.app
        (freeLinearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) := by
  let L := (normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)
  let K := L.extend ComplexShape.embeddingDownNat
  let h := (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).hom.app L ≫
    Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).hom.app
      (freeLinearizedSimplicialWeight A W.flip))
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))
  have he : complexOfFunctorsToFunctorToComplex.map
      ((functorComplexExchangeCounitIso J (ModuleCat A) (.up ℤ)).inv.app K) =
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (complexOfFunctorsToFunctorToComplex.obj K) := by
    apply NatTrans.ext
    funext j
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  change complexOfFunctorsToFunctorToComplex.map
    ((functorComplexExchangeCounitIso J (ModuleCat A) (.up ℤ)).inv.app K ≫
      (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).map h) =
    h ≫ (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app _
  rw [CategoryTheory.Functor.map_comp, he]
  exact ((functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.naturality h).symm
/-- 元の線形重み比較の順射は点ごとの同じ係数移送を厳密に与える。 -/
theorem normalizedLinearWeightDiagramIso_hom_evaluation (W : J ⥤ SSet.{0}) :
    Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).inv.app
        (linearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).inv.app
        ((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)) ≫
      complexOfFunctorsToFunctorToComplex.map (normalizedLinearWeightDiagramIso A W).hom =
    Functor.whiskerRight ((pointwiseMooreFunctor J (ModuleCat A)).map
        (linearizedSimplicialWeightFreeIso A W.flip).hom)
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) := by
  let V := linearizedSimplicialWeight A W.flip
  let U := freeLinearizedSimplicialWeight A W.flip
  let g : V ⟶ U := (linearizedSimplicialWeightFreeIso A W.flip).hom
  let T := (Functor.whiskeringRight J (ChainComplex (ModuleCat A) ℕ)
    (CochainComplex (ModuleCat A) ℤ)).obj (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))
  let a := complexOfFunctorsToFunctorToComplex.map ((normalizedMooreComplex _).map g)
  let b := (pointwiseMooreFunctor J (ModuleCat A)).map g
  let α := pointwiseMooreIso J (ModuleCat A)
  let β := pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat
  let u := (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
    (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
  have hb := β.hom.naturality ((normalizedMooreComplex _).map g)
  change complexOfFunctorsToFunctorToComplex.map (normalizedLinearWeightFreeIso A W.flip).hom ≫
    β.hom.app ((normalizedMooreComplex _).obj U) =
    β.hom.app ((normalizedMooreComplex _).obj V) ≫ T.map a at hb
  have hb' : β.inv.app ((normalizedMooreComplex _).obj V) ≫
      complexOfFunctorsToFunctorToComplex.map (normalizedLinearWeightFreeIso A W.flip).hom ≫
      β.hom.app ((normalizedMooreComplex _).obj U) = T.map a := by
    rw [hb, Iso.inv_hom_id_app_assoc]
  have ha := α.hom.naturality g
  change a ≫ α.hom.app U = α.hom.app V ≫ b at ha
  have ha' : T.map (α.inv.app V) ≫ T.map a ≫ T.map (α.hom.app U) = T.map b := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    erw [ha, Iso.inv_hom_id_app_assoc]
  rw [normalizedLinearWeightDiagramIso, Iso.trans_hom, Functor.map_comp,
    freeLinearWeightDiagramIso_hom_evaluation]
  change T.map (α.inv.app V) ≫ β.inv.app ((normalizedMooreComplex _).obj V) ≫
      (complexOfFunctorsToFunctorToComplex.map (normalizedLinearWeightFreeIso A W.flip).hom ≫
        (β.hom.app ((normalizedMooreComplex _).obj U) ≫ T.map (α.hom.app U) ≫ u)) = T.map b ≫ u
  calc
    _ = T.map (α.inv.app V) ≫ T.map a ≫ T.map (α.hom.app U) ≫ u := by
      simpa only [Category.assoc] using
        congrArg (fun t => T.map (α.inv.app V) ≫ t ≫ T.map (α.hom.app U) ≫ u) hb'
    _ = _ := by simpa only [Category.assoc] using congrArg (fun t => t ≫ u) ha'
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
