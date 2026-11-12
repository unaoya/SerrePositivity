module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullback
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism
public import SerrePositivity.AlgebraicGeometry.ModuleCechScalarExtension

/-!
概要：基底環を動かす実際の構造層の引き戻しを、係数図式の射として作る。
方針：構造射の可換性とスカラー制限の合成の同型を用い、随伴で延長する。
規約：空交叉でも射は存在するが、同型性は非空のアフィン交叉でだけ使う。
使われ方：平坦底変換、閉厚化、模型の遷移の同じ射に対する比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] (α : R →+* A)
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X) (h : g ≫ iX = iY ≫ Spec.map (CommRingCat.ofHom α))

/-- 基底環の変わる構造層の引き戻し。スカラー制限の合成を明示する。 -/
def schemeStructureCechBaseChangePullbackCoefficient :
    schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars (schemeScalarHom X iX) ⟶
      (Opens.map g.base).op ⋙ (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) ⋙ ModuleCat.restrictScalars α :=
  schemeStructureCechPullbackCoefficient g (schemeScalarHom X iX)
      ((schemeScalarHom Y iY).comp α) (schemeScalarHom_naturality X g iX iY α h) ≫
    Functor.whiskerLeft (Opens.map g.base).op
      (Functor.isoWhiskerLeft (schemeStructureCechPresheaf Y)
        (ModuleCat.restrictScalarsComp α (schemeScalarHom Y iY))).hom

variable {ι : Type} [DecidableEq ι]

/-- 実際の基底変更から得る、逆像被覆の係数図式への射。 -/
def schemeStructureCechBaseChangeDiagramRestriction (U : ι → X.Opens) :
    openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
      ModuleCat.restrictScalars (schemeScalarHom X iX)) U ⟶
      openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) (fun i ↦ g ⁻¹ᵁ U i) ⋙
          ModuleCat.restrictScalars α :=
  openCoverCechCoefficientMap
      (schemeStructureCechBaseChangePullbackCoefficient α iX iY g h) U ≫
    (schemeCechPreimageCoefficientIso g
      ((schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars (schemeScalarHom Y iY)) ⋙
        ModuleCat.restrictScalars α) U).hom

/-- 実際の切断の引き戻しをテンソル積から延長した、自然な係数の射。 -/
def schemeStructureCechBaseChangeDiagramMap (U : ι → X.Opens) :
    openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
      ModuleCat.restrictScalars (schemeScalarHom X iX)) U ⋙ ModuleCat.extendScalars α ⟶
      openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) (fun i ↦ g ⁻¹ᵁ U i) :=
  moduleCechScalarExtension α (schemeStructureCechBaseChangeDiagramRestriction α iX iY g h U)

end SerrePositivity.AlgebraicGeometry
