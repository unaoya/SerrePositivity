module
public import SerrePositivity.KST.SConstruction.DGHomGluingConePrimitiveDifferential
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeHomMap

/-! # 元の gluing Hom から実 cone Hom への鎖写像
概要：元の三成分を同じ実 end 内の cone 作用に送る全 Hom 鎖写像を構成する。
方針：三成分の線形性と、元の第三成分の捻れた微分式を合成する。
規約：単位・合成保存の包装は別工程。使われ方：元の対象族の実 dg 関手化。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 同じ三成分作用は元の gluing の捻れた微分を保つ実 Hom 鎖写像。 -/
def dgHomGluingConeHomMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y ⟶
      homObject R (PerfectDGModule R E) (dgHomGluingTargetCone R C D E p q X)
        (dgHomGluingTargetCone R C D E p q Y) :=
  dgGluingModuleConeHomMap R E
    (dgHomGluingTargetModuleMap R C D E p q X)
    (dgHomGluingTargetModuleMap R C D E p q Y)
    (dgHomGluingConeLeftMap R C D E p q X Y)
    (dgHomGluingConeRightMap R C D E p q X Y)
    (dgHomGluingConePrimitive R C D E p q X Y)
    (dgHomGluingConePrimitive_differential R C D E p q X Y)

/-- 実 Hom 鎖写像は元の左右成分と第三比較を持つ同じ end 元を回収する。 -/
lemma dgHomGluingConeHomMap_apply (n : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y).X n) :
    (dgHomGluingConeHomMap R C D E p q X Y).f n a =
      dgGluingModuleConeElement R E
        (dgHomGluingTargetModuleMap R C D E p q X)
        (dgHomGluingTargetModuleMap R C D E p q Y)
        ((dgHomGluingConeLeftMap R C D E p q X Y).f n a)
        ((dgHomGluingConeRightMap R C D E p q X Y).f n a)
        ((dgHomGluingConePrimitive R C D E p q X Y).v n (n - 1) (by omega) a)
        (by omega) := rfl

end SerrePositivity.KST.SConstruction
