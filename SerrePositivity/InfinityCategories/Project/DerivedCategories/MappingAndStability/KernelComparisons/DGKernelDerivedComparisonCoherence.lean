module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedComparisonAction
/-!
概要：元の一般準同型の span 比較と実導来射作用を同じ全関手射で照合する。
方針：実切断の二合成と同じ関手の恒等・合成則を使う。
規約：従来の指定比較を保つ。使われ方：模型変更の自然性と合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedInfinity_comparison_id (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E (𝟙 P)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D).id_mem P) = Iso.refl _ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_eq_mapIso]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedQuasiIsoMapIso_id R D E P
lemma dgKernelDerivedInfinity_comparison_comp
    {P Q S : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q) (g : Q ⟶ S)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) (hg : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E (f ≫ g)
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D).comp_mem f g hf hg) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E g hg := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_eq_mapIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_eq_mapIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_eq_mapIso]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedQuasiIsoMapIso_comp R D E f g hf hg
lemma dgKernelDerivedInfinity_comparison_of_iso
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E e.hom
      (by intro x y; infer_instance) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_eq_mapIso]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedQuasiIsoMapIso_of_iso R D E e
lemma dgKernelDerivedInfinity_comparison_naturality
    {P P' Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) (hg : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D g)
    (a : P ⟶ Q) (b : P' ⟶ Q') (h : f ≫ b = a ≫ g) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map b =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map a ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E g hg).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_hom,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
