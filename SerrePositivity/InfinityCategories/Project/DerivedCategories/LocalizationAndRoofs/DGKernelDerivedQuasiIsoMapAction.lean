module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGKernelDerivedQuasiIsoMapInvertible
/-!
概要：準同型の元の導来射を順方向に持つ同型と、その恒等・合成則を回収する。
方針：同じ射の可逆性と元の h Fun 値関手の関手性を使う。
規約：従来の span 比較との同定は別途行う。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
def dgKernelDerivedQuasiIsoMapIso
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor_map_isIso_of_quasiIso R D E f hf
  exact asIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f)
lemma dgKernelDerivedQuasiIsoMapIso_hom
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    (dgKernelDerivedQuasiIsoMapIso R D E f hf).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f := by rfl
lemma dgKernelDerivedQuasiIsoMapIso_id (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    dgKernelDerivedQuasiIsoMapIso R D E (𝟙 P) ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D).id_mem P) =
      Iso.refl _ := by
  apply Iso.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map (𝟙 P) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _
lemma dgKernelDerivedQuasiIsoMapIso_comp
    {P Q S : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q) (g : Q ⟶ S)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) (hg : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D g) :
    dgKernelDerivedQuasiIsoMapIso R D E (f ≫ g)
        ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D).comp_mem f g hf hg) =
      dgKernelDerivedQuasiIsoMapIso R D E f hf ≪≫ dgKernelDerivedQuasiIsoMapIso R D E g hg := by
  apply Iso.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map (f ≫ g) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g
  exact CategoryTheory.Functor.map_comp _ _ _
lemma dgKernelDerivedQuasiIsoMapIso_of_iso {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    dgKernelDerivedQuasiIsoMapIso R D E e.hom (by intro x y; infer_instance) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e := by
  apply Iso.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map e.hom = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor_mapIso]
  rfl
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
