module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeDerivedHomInfinity
/-!
概要：共変・反変の実 D(R) 値 Hom の値を、元の同じ全 Hom 複体への半自由分解として回収する。
方針：厳密切断から得た同じ augmentation を、一対象 R 加群で評価する。
規約：準同型は全整数次数で検証。使われ方：実写像空間との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ実共変 Hom 関手の値となる、実半自由 R 加群。 -/
def dgSemifreeDerivedHomValue (P Q : SemifreeDGModules R D) : SemifreeDGModules R PUnit.{1} :=
  dgModuleOutputResolutionValue R (SemifreeDGModules R D) PUnit.{1}
    (dgSemifreeHomTargetModuleDG R D P) Q
/-- 同じ実反変 Hom 関手の値となる、実半自由 R 加群。 -/
def dgSemifreeDerivedHomSourceValue (P Q : SemifreeDGModules R D) :
    SemifreeDGModules R PUnit.{1} :=
  dgModuleOutputResolutionValue R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
    (dgSemifreeHomSourceModuleDG R D Q) (Opposite.op P)
/-- 共変 Hom の同じ値から、元の全 Hom end 複体への実鎖写像。 -/
def dgSemifreeDerivedHomAugmentation (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedHomValue R D P Q).val.obj (Opposite.op PUnit.unit) ⟶
      moduleHom R D P.val Q.val :=
  (moduleEvaluation R PUnit.{1} PUnit.unit).map
    (dgModuleOutputResolutionAugmentation R (SemifreeDGModules R D) PUnit.{1}
      (dgSemifreeHomTargetModuleDG R D P) Q)
/-- 反変 Hom の同じ値からも、元の同じ全 Hom end 複体へ写す。 -/
def dgSemifreeDerivedHomSourceAugmentation (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedHomSourceValue R D P Q).val.obj (Opposite.op PUnit.unit) ⟶
      moduleHom R D P.val Q.val :=
  (moduleEvaluation R PUnit.{1} PUnit.unit).map
    (dgModuleOutputResolutionAugmentation R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
      (dgSemifreeHomSourceModuleDG R D Q) (Opposite.op P))
/-- 共変 Hom の同じ実 augmentation は、全次数で準同型。 -/
lemma dgSemifreeDerivedHomAugmentation_quasiIso (P Q : SemifreeDGModules R D) :
    QuasiIso (dgSemifreeDerivedHomAugmentation R D P Q) :=
  dgModuleOutputResolutionAugmentation_quasiIso R (SemifreeDGModules R D) PUnit.{1}
    (dgSemifreeHomTargetModuleDG R D P) Q PUnit.unit
/-- 反変 Hom の同じ実 augmentation も、全次数で準同型。 -/
lemma dgSemifreeDerivedHomSourceAugmentation_quasiIso (P Q : SemifreeDGModules R D) :
    QuasiIso (dgSemifreeDerivedHomSourceAugmentation R D P Q) :=
  dgModuleOutputResolutionAugmentation_quasiIso R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
    (dgSemifreeHomSourceModuleDG R D Q) (Opposite.op P) PUnit.unit
/-- 共変 Hom の実 augmentation は、各整数次数で全射。 -/
lemma dgSemifreeDerivedHomAugmentation_surjective (P Q : SemifreeDGModules R D) (n : ℤ) :
    Function.Surjective ((dgSemifreeDerivedHomAugmentation R D P Q).f n) :=
  dgModuleOutputResolutionAugmentation_degree_surjective R (SemifreeDGModules R D)
    PUnit.{1} (dgSemifreeHomTargetModuleDG R D P) Q PUnit.unit n
/-- 反変 Hom の実 augmentation も、各整数次数で全射。 -/
lemma dgSemifreeDerivedHomSourceAugmentation_surjective
    (P Q : SemifreeDGModules R D) (n : ℤ) :
    Function.Surjective ((dgSemifreeDerivedHomSourceAugmentation R D P Q).f n) :=
  dgModuleOutputResolutionAugmentation_degree_surjective R (SemifreeDGModules R D)ᵒᵖ
    PUnit.{1} (dgSemifreeHomSourceModuleDG R D Q) (Opposite.op P) PUnit.unit n
/-- 共変 Hom 関手の頂点値は、同じ実半自由分解の値。 -/
lemma dgSemifreeDerivedHomTargetInfinity_vertex (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedHomTargetInfinity R D P).app (Opposite.op ⦋0⦌) (Simplex.vertex Q) =
      Simplex.vertex ((dgUniverseLiftUp R (SemifreeDGModules R PUnit.{1})).obj
        (dgSemifreeDerivedHomValue R D P Q)) :=
  dgModuleOutputResolutionInfinity_vertex R (SemifreeDGModules R D) PUnit.{1}
    (dgSemifreeHomTargetModuleDG R D P) Q
/-- 実反対 ∞ 圏からの反変 Hom の頂点値も、同じ実半自由分解の値。 -/
lemma dgSemifreeDerivedContravariantHomInfinity_vertex (P Q : SemifreeDGModules R D) :
    (dgSemifreeDerivedContravariantHomInfinity R D Q).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (Simplex.vertex P : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)) =
      Simplex.vertex ((dgUniverseLiftUp R (SemifreeDGModules R PUnit.{1})).obj
        (dgSemifreeDerivedHomSourceValue R D P Q)) := by
  change (dgSemifreeDerivedHomSourceDGopInfinity R D Q).app (Opposite.op ⦋0⦌)
    ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm
        (Simplex.vertex P : (dgModuleDerivedInfinityCategory R D) _⦋0⦌))) = _
  rw [dgNerveOppositeIso_hom_vertex]
  exact dgModuleOutputResolutionInfinity_vertex R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
    (dgSemifreeHomSourceModuleDG R D Q) (Opposite.op P)
end SerrePositivity.InfinityCategories
