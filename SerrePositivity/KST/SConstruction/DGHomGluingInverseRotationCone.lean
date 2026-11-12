module
public import SerrePositivity.KST.SConstruction.DGModuleInverseRotationCone
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotation

/-!
概要：元 Hom gluing の実逆回転の元加群 cone を、元右対象の代表加群へ比較する。
方針：同じ connecting 射・実 dg shift を指定加群比較へ特殊化する。
規約：小基底の Yoneda 評価前の実加群比較。全関手族の自然性は別工程。
使われ方：中央射と実差の合成比較を構成する指定成分。
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

/-- 概要：元実逆回転比較は同じ connecting 射の実加群逆 shift。
方針：元 dg shift の閉射回収を使用する。
規約：元閉射の等号。使われ方：同じ実 cone の型照合。 -/
lemma dgHomGluingInverseRotationModuleMap_eq (X : L) :
    dgHomGluingInverseRotationModuleMap R C D E p q X =
      moduleShiftMap R E (-1)
        (moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q X)) :=
  moduleShiftDG_map_eq R E (-1) _

/-- 概要：同じ実逆回転の元 cone と実加群 shift 表示の cone の厳密照合。
方針：同じ元閉射の等号だけを cone に適用する。
規約：元実 cone の始域を保持。使われ方：指定比較射の型輸送。 -/
def dgHomGluingInverseRotationConeInputIso (X : L) :
    moduleCone R E (dgHomGluingInverseRotationModuleMap R C D E p q X) ≅
      moduleCone R E (moduleShiftMap R E (-1)
        (moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q X))) :=
  eqToIso (congrArg (fun a => moduleCone R E a)
    (dgHomGluingInverseRotationModuleMap_eq R C D E p q X))

/-- 概要：元実逆回転比較の同じ元加群 cone から元右対象への指定射。
方針：元閉射の厳密照合と同じ実逆回転 cone 比較を合成する。
規約：対象別の同型存在を選択しない。使われ方：中央射・実差の合成比較成分。 -/
def dgHomGluingInverseRotationConeComparison (X : L) :
    moduleCone R E (dgHomGluingInverseRotationModuleMap R C D E p q X) ⟶
      ForgetEnrichment.of (Complex R) (representable R (q.obj X.right)) :=
  (dgHomGluingInverseRotationConeInputIso R C D E p q X).hom ≫
    dgModuleInverseRotationConeComparison R E (dgHomGluingTargetModuleMap R C D E p q X)

/-- 概要：同じ元実逆回転 cone 比較の K(E) 同値性。
方針：元の型輸送同型と指定逆回転比較の同値性を合成する。
規約：全関手族の自然性は別途必要。使われ方：native 全比較の成分認証。 -/
lemma dgHomGluingInverseRotationConeComparison_isIso (X : L) :
    IsIso ((moduleToHomotopy R E).map
      (dgHomGluingInverseRotationConeComparison R C D E p q X)) := by
  haveI := dgModuleInverseRotationConeComparison_isIso R E
    (dgHomGluingTargetModuleMap R C D E p q X)
  rw [dgHomGluingInverseRotationConeComparison, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
