module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatEdges
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdgePostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
/-!
概要：K-flat 入力の通常 tensor の出力を指定半自由分解へ送り、元の導来 kernel と比較する。
方針：両 K-flat 端点間の準同型保存と、同じ生の関手の因数分解同型を使う。
規約：kernel 自体の K-flat 性は不要。使われ方：実導来合成子と通常結合子の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- K-flat 入力に元の通常 tensor を適用し、同じ出力分解で導来模型へ送る実関手。 -/
def dgRelativeKFlatKernelToDerived (P : Bimodule R E D) :
    dgRelativeKFlatModuleNerve R D ⟶ dgModuleDerivedInfinityCategory R E :=
  dgRelativeKFlatModuleInclusion R D ≫
    (dgNerve.map (Morita.kernelTensor R D E P) ≫
      dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
/-- 任意 kernel の通常 tensor と出力分解は、K-flat 入力上の全準同型辺を反転する。 -/
lemma dgRelativeKFlatKernelToDerived_invertsQuasiIsomorphismEdges (P : Bimodule R E D) :
    InvertsEdges (dgRelativeKFlatKernelToDerived R D E P)
      (dgRelativeKFlatQuasiIsomorphismEdges R D) := by
  apply dgRelativeKFlatQuasiIsomorphismEdges_inverts R D
  intro M N hM hN f hf
  apply (dgClosedEdge_postcomposition_isInvertible_iff R (RightModule R D) (RightModule R E)
    (Morita.kernelTensor R D E P)
    (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))) f).mpr
  exact dgModuleResolution_invertsQuasiIsomorphismEdges R E
    ⟨_, _, (Morita.kernelTensor R D E P).onClosed.map f,
      Morita.kernelTensor_relativeKFlat_quasiIso R D E P hM hN f hf, rfl⟩
/-- 元の指定導来 kernel 関手は、同じ K-flat 入力作用の半自由包含への制限と全関手同型。 -/
def dgKernelDerivedInfinity_relativeKFlatRestrictionIso (P : Bimodule R E D) :
    FunctorIso (dgKernelDerivedInfinity R D E P)
      (dgSemifreeToRelativeKFlatNerve R D ≫ dgRelativeKFlatKernelToDerived R D E P) := by
  have h := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P)
  simpa only [dgRelativeKFlatKernelToDerived, ← Category.assoc,
    dgSemifreeToRelativeKFlatNerve_inclusion, dgSemifreeKernelModuleDG, dgNerve.map_comp] using! h
end SerrePositivity.InfinityCategories
