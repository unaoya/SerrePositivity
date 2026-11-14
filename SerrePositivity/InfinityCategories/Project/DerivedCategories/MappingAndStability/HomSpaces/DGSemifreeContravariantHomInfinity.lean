module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeHomComplexInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeIso
/-!
概要：固定終域の全 Hom 複体を、実導来 ∞ 圏の単体的反対圏からの ∞ 関手にする。
方針：実 dg 反対 nerve の厳密比較を、同じ dg 代表関手へ前合成する。
規約：値域は複体の dg nerve。D(R) への移行と tensor–Hom 随伴は別工程。
使われ方：β5 の反変 Hom の全高次関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 固定終域の全 Hom 複体は、実導来 ∞ 圏の反対圏からの全単体を保つ関手。 -/
def dgSemifreeContravariantHomInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomComplexNerve R D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceInfinity R D Q
/-- 同じ実反変 Hom 関手の頂点値は、元の全 Hom end 複体。 -/
lemma dgSemifreeContravariantHomInfinity_vertex (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgSemifreeContravariantHomInfinity R D Q).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (Complex R)).obj (moduleHom R D P.val Q.val)) :
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomComplexNerve R D) _⦋0⦌) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceInfinity R D Q).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceDG R D Q) (Opposite.op P)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
