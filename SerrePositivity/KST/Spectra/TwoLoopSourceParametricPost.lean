module

public import SerrePositivity.KST.Spectra.TwoLoopSourceCoordinates
public import SerrePositivity.KST.Spectra.PointedParametricPostCurry

/-!
概要：混合源の同じ二重 curry が、標準の三つの ihomAction による全族作用と可換と示す。
方針：テンソル curry の全族自然性を二段に適用し、同じ mappingIso の合成へ戻す。
規約：全単体の射の厳密等式。使われ方：通常円交換族の標準全族作用の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.TwoLoopSource
variable (S : PointedSimplicialSet.{u}) {P Z Z' : PointedSimplicialSet.{u}}
  (v : P ⟶ PointedObject.basedHom Z Z')

/-- 元の内側の源と二つの外側の円へ、標準の ihomAction を反復した同じ全族作用。 -/
def standardParametricPost : LoopExchangePaths.doubleLoop (PointedObject.basedHom S Z) ⟶
    PointedObject.basedHom P (LoopExchangePaths.doubleLoop (PointedObject.basedHom S Z')) :=
  PointedMapping.parametricPost CirclePower.space.{u}
    ((v ≫ PointedMapping.ihomAction S Z Z') ≫ PointedMapping.ihomAction CirclePower.space.{u}
      (PointedObject.basedHom S Z) (PointedObject.basedHom S Z'))

/-- 元の同じ mappingIso は、混合源の後合成族と標準の反復作用に全単体で厳密に可換。 -/
lemma mappingIso_standardParametricPost :
    PointedMapping.parametricPost (source S) v ≫ PointedObject.basedHomMap P (mappingIso S Z').hom =
      (mappingIso S Z).hom ≫ standardParametricPost S v := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  have h₁ := PointedMapping.parametricPost_tensor S (K ⊗ K) v
  have h₂ := PointedMapping.parametricPost_tensor K K (v ≫ PointedMapping.ihomAction S Z Z')
  have hm : PointedObject.basedHomMap P (mappingIso S Z').hom =
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z').hom ≫
        PointedObject.basedHomMap P
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K (PointedObject.basedHom S Z')).hom := by
    change (ihom P).map ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z').hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K (PointedObject.basedHom S Z')).hom) = _
    exact CategoryTheory.Functor.map_comp (ihom P) _ _
  calc
    _ = (PointedMapping.parametricPost (source S) v ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z').hom) ≫
          PointedObject.basedHomMap P
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K (PointedObject.basedHom S Z')).hom := by
      rw [hm, Category.assoc]
    _ = ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
        PointedMapping.parametricPost (K ⊗ K) (v ≫ PointedMapping.ihomAction S Z Z')) ≫
          PointedObject.basedHomMap P
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K (PointedObject.basedHom S Z')).hom := by rw [h₁]
    _ = (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S (K ⊗ K) Z).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K K (PointedObject.basedHom S Z)).hom ≫
          PointedMapping.parametricPost K ((v ≫ PointedMapping.ihomAction S Z Z') ≫
            PointedMapping.ihomAction K (PointedObject.basedHom S Z)
              (PointedObject.basedHom S Z')) := by rw [Category.assoc, h₂]
    _ = _ := rfl

end SerrePositivity.KST.Spectra.TwoLoopSource
