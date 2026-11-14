module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorProductMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSemifreeHomTensorValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeIso
/-!
概要：元の導来 ∞ 圏の実反対と元の圏の直積から、同じ D(R) 値 Hom の全 ∞ 関手を作る。
方針：全 HA を持つ tensor 単体の実写像と、同じ実出力分解の ∞ 関手を合成する。
規約：元の出力の射影性を仮定しない。使われ方：二変数 Hom と固定入力比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory Opposite
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
def dgSemifreeDerivedHomProductDGopInfinity :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorProductMap R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
def dgSemifreeDerivedHomBivariateInfinity :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedNerve R D :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ⊗ₘ 𝟙 _) ≫
    dgSemifreeDerivedHomProductDGopInfinity R D
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
lemma dgSemifreeDerivedHomProductDGopInfinity_app {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) n) :
    (dgSemifreeDerivedHomProductDGopInfinity R D).app (_root_.Opposite.op ⦋n⦌) (s, t) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D).app (_root_.Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSimplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) s t) := rfl
/-- 元の二入力の全単体作用と同じ実半自由 Hom 値の構成。 -/
lemma dgSemifreeDerivedHomBivariateInfinity_vertex (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgSemifreeDerivedHomBivariateInfinity R D).app (_root_.Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R PUnit.{1})).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorValue R D P Q)) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D).app (_root_.Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSimplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom.app (_root_.Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSimplex_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity_vertex R D P Q

end SerrePositivity.InfinityCategories.Project.DerivedCategories
