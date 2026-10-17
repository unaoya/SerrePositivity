module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedUnitAll

/-! # 明示したcompact生成仮定の下での主導来圏全体の再構成同値

thick生成だけから全導来圏同値は結論しない。指定対象によるcompact生成と、
外部compact⇒Perf入力をそれぞれ明示して受け取る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
variable (hCG : endomorphismCompactGenerator A D E.val)
include compactToPerfect hgen hCG

/-- 単位の全対象での可逆性、右三角恒等式、Homの保守性から余単位も可逆となる。 -/
lemma endomorphismDerivedCounit_isIso_all (X : DerivedModuleCategory A D) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app X) := by
  let adj := endomorphismDerivedAdjunction A D E.val E.property.1
  let R := endomorphismDerivedHom A D E.val E.property.1
  let := endomorphismDerivedUnit_isIso_all A D S E compactToPerfect hgen (R.obj X)
  have hu : IsIso (adj.unit.app (R.obj X)) := by
    change IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app (R.obj X))
    infer_instance
  let := hu
  have he : R.map (adj.counit.app X) = inv (adj.unit.app (R.obj X)) := by
    apply (cancel_epi (adj.unit.app (R.obj X))).1
    rw [adj.right_triangle_components, IsIso.hom_inv_id]
    rfl
  have hm : IsIso (R.map (adj.counit.app X)) := by rw [he]; infer_instance
  let := hm
  exact endomorphismDerivedHom_reflectsIso A D E.val E.property.1 hCG (adj.counit.app X)

/-- 実際の導来tensorとHomを両方向に持つ同値。 -/
def endomorphismDerivedEquivalence :
    DerivedModuleCategory A (EndomorphismObject E.val) ≌ DerivedModuleCategory A D := by
  letI (N : DerivedModuleCategory A (EndomorphismObject E.val)) :
      IsIso ((endomorphismDerivedAdjunction A D E.val E.property.1).unit.app N) :=
    endomorphismDerivedUnit_isIso_all A D S E compactToPerfect hgen N
  letI (X : DerivedModuleCategory A D) :
      IsIso ((endomorphismDerivedAdjunction A D E.val E.property.1).counit.app X) :=
    endomorphismDerivedCounit_isIso_all A D S E compactToPerfect hgen hCG X
  exact (endomorphismDerivedAdjunction A D E.val E.property.1).toEquivalence

lemma endomorphismDerivedEquivalence_functor :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor =
      endomorphismDerivedTensor A D E.val := rfl

lemma endomorphismDerivedEquivalence_inverse :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).inverse =
      endomorphismDerivedHom A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_unit :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).unitIso.hom =
      endomorphismDerivedUnit A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_counit :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).counitIso.hom =
      endomorphismDerivedCounit A D E.val E.property.1 := rfl

end SerrePositivity.DifferentialGraded
