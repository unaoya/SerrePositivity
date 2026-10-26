module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityHomTargetDiagonal
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetContraction
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor
public import SerrePositivity.InfinityCategories.Derived.ContractingZeroVertex
/-!
概要：恒等 Hom gluing の元対角を、同じ実 cone 関手が native perfect 圏で零化する。
方針：同じ恒等閉比較の既存収縮元を全 Hom と微分を変えずに使う。
規約：零化だけの判定。全 cone 関手比較は局所化判定へ別に接続する。
使われ方：恒等 cone 差の対角零化条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id (A := R) C
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingIdentityConeDiagonal_vertex_zero (x : C) :
    IsZeroVertex (X := dgNerve R (PerfectDGModule R C))
      (Simplex.vertex ((dgHomGluingConeFunctor R C C C I I).obj
        ((dgGluingIdentityNativeDiagonal.{u, 0} R C).obj x))) := by
  apply dgNerve_contractingElement_isZeroVertex _
    (dgHomGluingTargetConeContractingElement R C C C I I
      ((dgGluingIdentityNativeDiagonal.{u, 0} R C).obj x) (Iso.refl _)
      (dgGluingIdentityNativeDiagonal_targetMap.{u, 0} R C x))
  exact dgHomGluingTargetConeContractingElement_d R C C C I I
    ((dgGluingIdentityNativeDiagonal.{u, 0} R C).obj x) (Iso.refl _)
    (dgGluingIdentityNativeDiagonal_targetMap.{u, 0} R C x)

end SerrePositivity.InfinityCategories
