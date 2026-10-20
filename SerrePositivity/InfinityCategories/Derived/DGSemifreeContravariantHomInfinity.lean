module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomComplexInfinity
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 固定終域の全 Hom 複体は、実導来 ∞ 圏の反対圏からの全単体を保つ関手。 -/
def dgSemifreeContravariantHomInfinity (Q : SemifreeDGModules R D) :
    (dgModuleDerivedInfinityCategory R D).op ⟶ dgHomComplexNerve R D :=
  (dgNerveOppositeIso R (SemifreeDGModules R D)).hom ≫ dgSemifreeHomSourceInfinity R D Q
/-- 同じ実反変 Hom 関手の頂点値は、元の全 Hom end 複体。 -/
lemma dgSemifreeContravariantHomInfinity_vertex (P Q : SemifreeDGModules R D) :
    (dgSemifreeContravariantHomInfinity R D Q).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (Simplex.vertex P : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)) =
        (Simplex.vertex ((dgUniverseLiftUp R (Complex R)).obj (moduleHom R D P.val Q.val)) :
          (dgHomComplexNerve R D) _⦋0⦌) := by
  change (dgSemifreeHomSourceInfinity R D Q).app (Opposite.op ⦋0⦌)
    ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm
        (Simplex.vertex P : (dgModuleDerivedInfinityCategory R D) _⦋0⦌))) = _
  rw [dgNerveOppositeIso_hom_vertex]
  exact dgFunctorNerve_vertex (dgSemifreeHomSourceDG R D Q) (Opposite.op P)
end SerrePositivity.InfinityCategories
