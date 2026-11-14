module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGKernelTensorIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGModuleResolvedRawFactorAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
/-!
概要：元の指定した一般 kernel の実導来比較は、恒等・通常順合成・指定逆を保つ。
方針：通常 tensor の同じ比較と入力前合成、出力分解への同型輸送を端点ごと照合する。
規約：既存の比較定義と実関手を保持する。使われ方：合成子・模型変更の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の指定 kernel の実導来比較は、同じ全関手圏で通常順合成を保つ。 -/
lemma dgKernelDerivedInfinity_bimoduleIso_trans
    {P Q S : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) (f : Q ≅ S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (e ≪≫ f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E f := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso_trans]
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso_trans]
  congr 1
/-- 元の指定 kernel の実導来比較は、同じ全関手圏で恒等を保つ。 -/
lemma dgKernelDerivedInfinity_bimoduleIso_refl (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E (Iso.refl P) = Iso.refl _ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorIsoNerveOfBimoduleIso_refl]
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  simp only [Functor.mapIso_refl]
  simpa using! _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso_refl R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
/-- 元の指定 kernel の実導来比較は、同じ全関手圏で指定逆同型を保つ。 -/
lemma dgKernelDerivedInfinity_bimoduleIso_symm
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e.symm =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e).symm := by
  have ht := dgKernelDerivedInfinity_bimoduleIso_trans R D E e e.symm
  rw [Iso.self_symm_id, dgKernelDerivedInfinity_bimoduleIso_refl] at ht
  have he := congrArg (fun z =>
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e).symm ≪≫ z) ht
  simp only [Iso.trans_refl, Iso.symm_self_id_assoc] at he
  exact he.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
