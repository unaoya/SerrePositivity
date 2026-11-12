module
public import SerrePositivity.KST.SConstruction.DGHomGluingLoopCone
public import SerrePositivity.KST.SConstruction.DGModuleLoopConeProjection

/-!
概要：元 Hom gluing の逆 shift cone から元左対象への射を同じ小模型で保持する。
方針：元加群の connecting 射と指定 shift 比較から得た閉元を充満小模型へ移す。
規約：同じ実 cone・同じ左対象・同じ閉射を保持。使われ方：逆回転の全 Hom 比較の成分。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)
local notation "T" => DGHomGluingLoopConeBase R C D E p q

/-- 概要：同じ元逆 shift cone 射の閉元を元小模型の全 Hom 内に保持する。
方針：元全加群の閉射・閉元対応を、同じ充満 Hom 複体で読む。
規約：元の実射を保持。使われ方：逆回転比較の閉元成分。 -/
def dgHomGluingLoopConeProjectionCycle (X : L) : zeroCycles (homObject R (T)
    ((dgHomGluingLoopConeSmall R C D E p q).obj X)
    ((dgHomGluingLoopConeTarget R C D E p q).obj X)) :=
  (closedHomEquiv R (RightModule R E)
    (shiftModule (-1) (dgHomGluingTargetCone R C D E p q X).val)
    (representable R (p.obj X.left)))
    (dgModuleLoopConeProjection R E (dgHomGluingTargetModuleMap R C D E p q X))

/-- 概要：同じ小模型内の元逆 shift cone から元左対象への実閉射。
方針：同じ閉元の元閉零圏での対応を取る。
規約：全 Hom 自然性は別補題で検証。使われ方：逆回転の閉零比較成分。 -/
def dgHomGluingLoopConeProjection (X : L) :
    ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeSmall R C D E p q).obj X) ⟶
      ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeTarget R C D E p q).obj X) :=
  dgModuleLoopConeProjection R E (dgHomGluingTargetModuleMap R C D E p q X)
end SerrePositivity.KST.SConstruction
