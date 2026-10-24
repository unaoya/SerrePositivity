module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientTensorComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
/-!
概要：元の係数脚と Yoneda 後の kernelTensor を、異なる対象宇宙でも実関手同型で比較する。
方針：全 Hom 自然な右単位同型の prism を共通単体宇宙で評価し、頂点辺の可逆性を移す。
規約：元の対象宇宙・双加群・右単位同型を保持し、Small は元 C・D のみとする。
使われ方：D-14 到着前の係数脚の接続と、一般宇宙での完全性の移送に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalCategory SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
def dgGluingUniverseCoefficientTensorPrism :
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (dgNerve R D) ⊗ Δ[1] ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgNerve R (RightModule R C)) where
  app _ := ↾fun s => ULift.up ((dgGluingCoefficientTensorStrict R C D M).simplex
    s.1.down (SSet.stdSimplex.objEquiv s.2).toOrderHom)
  naturality _ _ f := by
    ext s
    apply ULift.ext
    exact (dgGluingCoefficientTensorStrict R C D M).simplex_pullback
      s.1.down (SSet.stdSimplex.objEquiv s.2).toOrderHom f.unop.toOrderHom

def dgGluingUniverseCoefficientTensorHomotopy :
    SSet.Homotopy
      (dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w}
        ((dgYoneda R D).comp (Morita.kernelTensor R D C M)))
      (dgGluingUniverseCoefficient R C D M) where
  h := dgGluingUniverseCoefficientTensorPrism R C D M
  h₀ := by
    ext n s
    apply ULift.ext
    apply Simplex.ext
    rfl
  h₁ := by
    ext n s
    apply ULift.ext
    apply Simplex.ext
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2

lemma dgGluingUniverseCoefficientTensorHomotopy_vertex_edge (d : D) :
    (simplicialHomotopyVertexEdge (dgGluingUniverseCoefficientTensorHomotopy R C D M)
      (ULift.up (Simplex.vertex d))).edge =
    (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v w}
      (dgModuleEdge R C (BimoduleTensor.rightUnitIso R C D M d).hom).toTruncated).edge := by
  apply ULift.ext
  apply dgSimplex1_ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    change compose R ((dgGluingCoefficientTensorStrict R C D M).app d).val
      ((((dgYoneda R D).comp (Morita.kernelTensor R D C M)).map d d).f 0
        (unitElement R d).val) (add_zero 0) = _
    rw [DGFunctor.map_unitElement, compose_unit]
    rfl

def dgGluingUniverseCoefficientTensorIso :
    FunctorIso
      (dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w}
        ((dgYoneda R D).comp (Morita.kernelTensor R D C M)))
      (dgGluingUniverseCoefficient R C D M) :=
  functorIsoOfPointwiseInvertibleHomotopy
    (dgGluingUniverseCoefficientTensorHomotopy R C D M) (by
      intro z
      obtain ⟨z⟩ := z
      obtain ⟨d, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
      apply (isInvertibleEdge_congr
        (dgGluingUniverseCoefficientTensorHomotopy_vertex_edge R C D M d)).mpr
      apply IsInvertibleEdge.ulift
      have h := dgModuleEdge_isIso_of_homotopy R C
        (BimoduleTensor.rightUnitIso R C D M d).hom (by infer_instance)
      exact (edgeToPathHomotopyCategory _).map_isIso
        (SSet.Truncated.HomotopyCategory₂.homMk
          (dgModuleEdge R C (BimoduleTensor.rightUnitIso R C D M d).hom).toTruncated))

def dgGluingUniverseCoefficientTensorCompositeIso :
    FunctorIso
      (dgGluingUniverseYoneda.{u, w, v} R D ≫
        dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
          (Morita.kernelTensor R D C M))
      (dgGluingUniverseCoefficient R C D M) := by
  have he : dgGluingUniverseYoneda.{u, w, v} R D ≫
      dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
        (Morita.kernelTensor R D C M) =
      dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w}
        ((dgYoneda R D).comp (Morita.kernelTensor R D C M)) := by
    exact dgGluingUniverseNerveMap_comp.{u, w, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
      (dgYoneda R D) (Morita.kernelTensor R D C M)
  rw [he]
  exact dgGluingUniverseCoefficientTensorIso R C D M

def dgGluingUniverseDerivedCoefficientTensorCompositeIso :
    FunctorIso
      ((dgGluingUniverseYoneda.{u, w, v} R D ≫
        dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
          (Morita.kernelTensor R D C M)) ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) :=
  (dgGluingUniverseCoefficientTensorCompositeIso R C D M).postcomp
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)

end SerrePositivity.InfinityCategories
