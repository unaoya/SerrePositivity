module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor

/-! # Universe lift preserves the whole parameter mapping space

The comparison is an actual simplicial isomorphism, natural in both
variables and compatible with composition of parameter families. It does
not assert coherent descent of a separately chosen family of values.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLiftParameterHom
variable (K P : SSet.{v})

def degreeEquiv (n : SimplexCategory) :
    ULift.{w, v} ((SimplexParameterHom.obj K P).obj (Opposite.op n)) ≃
      (SimplexParameterHom.obj (UniverseLift.obj.{w} K)
        (UniverseLift.obj.{w} P)).obj (Opposite.op n) where
  toFun x := UniverseLift.simplexTensorMap.{w, v} x.down
  invFun h := ⟨UniverseLift.lowerSimplexTensor.{w, v} h⟩
  left_inv x := ULift.ext (UniverseLift.lowerSimplexTensor_simplexTensorMap.{w, v} x.down)
  right_inv h := UniverseLift.simplexTensorMap_lowerSimplexTensor.{w, v} h

def iso : SSet.uliftFunctor.{w, v}.obj (SimplexParameterHom.obj K P) ≅
    SimplexParameterHom.obj (UniverseLift.obj.{w} K) (UniverseLift.obj.{w} P) :=
  NatIso.ofComponents (fun n => (degreeEquiv K P n.unop).toIso) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro x
    exact (UniverseLift.simplexTensorMap_operator θ.unop x.down).symm)

lemma naturality {K' P' : SSet.{v}} (i : K' ⟶ K) (q : P ⟶ P') :
    SSet.uliftFunctor.{w, v}.map (SimplexParameterHom.map K P i q) ≫ (iso K' P').hom =
      (iso K P).hom ≫ SimplexParameterHom.map (UniverseLift.obj.{w} K)
        (UniverseLift.obj.{w} P) (UniverseLift.map i) (UniverseLift.map q) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro y
  rfl

lemma composition (Q : SSet.{v}) :
    (UniverseLift.tensorIso.{w} (SimplexParameterHom.obj K P)
        (SimplexParameterHom.obj P Q)).inv ≫
      SSet.uliftFunctor.{w, v}.map (SimplexParameterHom.composition K P Q) ≫ (iso K Q).hom =
    ((iso K P).hom ⊗ₘ (iso P Q).hom) ≫
      SimplexParameterHom.composition (UniverseLift.obj.{w} K) (UniverseLift.obj.{w} P)
        (UniverseLift.obj.{w} Q) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro y
  rfl

lemma identity (n : SimplexCategory) :
    UniverseLift.simplexTensorMap.{w, v} (SimplexParameterHom.identityFamily K n) =
      SimplexParameterHom.identityFamily (UniverseLift.obj.{w} K) n := by
  ext m x
  rfl

def bifunctorIso : SimplexParameterHom.bifunctor.{v} ⋙ SSet.uliftFunctor.{w, v} ≅
    (SSet.uliftFunctor.{w, v}.op.prod SSet.uliftFunctor.{w, v}) ⋙
      SimplexParameterHom.bifunctor.{max w v} :=
  NatIso.ofComponents (fun b => iso b.1.unop b.2) (by
    intro b c f
    exact naturality b.1.unop b.2 f.1.unop f.2)

def closedIso : SSet.uliftFunctor.{w, v}.obj ((ihom K).obj P) ≅
    (ihom (UniverseLift.obj.{w} K)).obj (UniverseLift.obj.{w} P) :=
  SSet.uliftFunctor.mapIso (SimplexParameterHom.nativeIso K P).symm ≪≫
    iso K P ≪≫ SimplexParameterHom.nativeIso (UniverseLift.obj K) (UniverseLift.obj P)

end SerrePositivity.SimplicialModel.UniverseLiftParameterHom
