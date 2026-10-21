module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedComparisonAction
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgKernelDerivedInfinity_comparison_id (P : BimoduleCategory R E D) :
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D E (𝟙 P)
      ((BimoduleCategory.quasiIso R E D).id_mem P) = Iso.refl _ := by
  rw [dgKernelDerivedInfinity_comparison_eq_mapIso]
  exact dgKernelDerivedQuasiIsoMapIso_id R D E P
lemma dgKernelDerivedInfinity_comparison_comp
    {P Q S : BimoduleCategory R E D} (f : P ⟶ Q) (g : Q ⟶ S)
    (hf : BimoduleCategory.quasiIso R E D f) (hg : BimoduleCategory.quasiIso R E D g) :
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D E (f ≫ g)
      ((BimoduleCategory.quasiIso R E D).comp_mem f g hf hg) =
      dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf ≪≫
        dgKernelDerivedInfinity_mapIso_of_quasiIso R D E g hg := by
  rw [dgKernelDerivedInfinity_comparison_eq_mapIso,
    dgKernelDerivedInfinity_comparison_eq_mapIso,
    dgKernelDerivedInfinity_comparison_eq_mapIso]
  exact dgKernelDerivedQuasiIsoMapIso_comp R D E f g hf hg
lemma dgKernelDerivedInfinity_comparison_of_iso
    {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D E e.hom
      (by intro x y; infer_instance) = dgKernelDerivedInfinity_bimoduleIso R D E e := by
  rw [dgKernelDerivedInfinity_comparison_eq_mapIso]
  exact dgKernelDerivedQuasiIsoMapIso_of_iso R D E e
lemma dgKernelDerivedInfinity_comparison_naturality
    {P P' Q Q' : BimoduleCategory R E D} (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : BimoduleCategory.quasiIso R E D f) (hg : BimoduleCategory.quasiIso R E D g)
    (a : P ⟶ Q) (b : P' ⟶ Q') (h : f ≫ b = a ≫ g) :
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf).hom ≫
        (dgKernelDerivedFunctorHomFunctor R D E).map b =
      (dgKernelDerivedFunctorHomFunctor R D E).map a ≫
        (dgKernelDerivedInfinity_mapIso_of_quasiIso R D E g hg).hom := by
  rw [dgKernelDerivedInfinity_comparison_hom, dgKernelDerivedInfinity_comparison_hom,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]
end SerrePositivity.InfinityCategories
