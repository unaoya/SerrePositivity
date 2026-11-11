module
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Module.Graded
/-!
概要：一般 dg 関手に沿う制限 Yoneda 双加群。
方針：全 Hom end の作用を同じ制限加群へ送る。
規約：元の全 dg 自然性と豊穣合成を保持する。
使われ方：選んだ加群代表部分圏の Yoneda 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory MonoidalCategory Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) [DGCategory R B] [Small.{u} B]
    (E : Type w) [DGCategory R E] (F : DGFunctor R B E)

def dgFunctorRestrictedRepresentable (X : E) : RightModule R B :=
  restrictModule R B E F.op (representable R X)

def dgFunctorRestrictedYonedaParam (X Y : E) :
    ModuleParamTrans R B (X ⟶[Complex R] Y)
      (dgFunctorRestrictedRepresentable R B E F X)
      (dgFunctorRestrictedRepresentable R B E F Y) :=
  moduleRestrictionParam R B E F.op (yonedaExtension R X (representable R Y) (𝟙 _))

def dgFunctorRestrictedYoneda : Bimodule R B E :=
  Bimodule.ofParamTrans R B E (dgFunctorRestrictedRepresentable R B E F)
    (dgFunctorRestrictedYonedaParam R B E F)
    (by
      intro X b
      change eId (Complex R) X ≫
        yonedaExtensionApp R X (representable R X) (𝟙 _) (F.op.obj b) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable R (F.obj b.unop)).map_id X)
    (by
      intro X Y Z b
      change eComp (Complex R) X Y Z ≫
          yonedaExtensionApp R X (representable R Z) (𝟙 _) (F.op.obj b) =
        (yonedaExtensionApp R X (representable R Y) (𝟙 _) (F.op.obj b) ⊗ₘ
          yonedaExtensionApp R Y (representable R Z) (𝟙 _) (F.op.obj b)) ≫
            enrichedComposition _ _ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable R (F.obj b.unop)).map_comp X Y Z)

end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
