module
public import SerrePositivity.InfinityCategories.Stable.QCatAdjunctionCompositeCounit
public import SerrePositivity.InfinityCategories.Stable.QCatAdjunctionTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionCounit
public import SerrePositivity.InfinityCategories.Derived.DGUniversalRightAdjunctionCounit
public import SerrePositivity.InfinityCategories.Derived.DGKernelAdjunction
public import SerrePositivity.InfinityCategories.Derived.DGKernelCounitCandidate
/-!
概要：元の一般 kernel 随伴の余単位を、元の指定候補そのものへ厳密に同定する。
方針：入力同値の三角式・随伴合成の式・指定端点輸送を同じ全関手上で照合する。
規約：元の実入力切断と比較同型を保持する。使われ方：一般 RHom の随伴整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel 随伴の余単位は、元の同じ指定候補と厳密に一致する。 -/
lemma dgKernelAdjunction_counitHom (P : Bimodule R E D) :
    (dgKernelAdjunction R D E P).counitHom = dgKernelCounitCandidate R D E P := by
  let C := SemifreeDGModules R D
  let F := dgSemifreeKernelModuleDG R D E P
  let T := DGModuleFunctorResolutionObject R C E F
  let G := dgModuleFunctorResolutionReplacement R C E F
  let R' := dgUniversalRightAdjointCandidate R T (SemifreeDGModules R E) G
    (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩)
  let a := dgUniversalRightAdjunction R T (SemifreeDGModules R E) G
    (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩)
  let b := (dgModuleResolvedSourceSectionEquivalence R C E F).toAdjunction
  have ha : HEq (dgKernelAdjunction R D E P) (b.comp a) := by
    unfold dgKernelAdjunction
    dsimp only [_root_.id]
    simp only [eq_mpr_eq_cast]
    exact HEq.trans (cast_heq _ _) (HEq.rfl)
  let e := ((dgModuleResolvedProjectionSectionIso R C E F).postcomp
    (dgNerve.map G)).precomp R'
  have he : HEq (dgKernelRightAdjointCompositeIso R D E P) e := by
    unfold dgKernelRightAdjointCompositeIso
    dsimp only [_root_.id]
    simp only [eq_mp_eq_cast, eq_mpr_eq_cast]
    exact HEq.trans (cast_heq _ _)
      (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) (HEq.rfl)))
  have hf : dgKernelDerivedInfinity R D E P =
      (dgModuleResolvedSourceSectionEquivalence R C E F).hom ≫ dgNerve.map G := by
    simpa only [dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  apply Arrow.mk_injective
  have h₀ := QCatAdjunction.counitHom_arrow_of_heq
    (dgKernelAdjunction R D E P) (b.comp a) hf rfl ha
  have h₁ := functorIso_hom_comp_arrow_of_heq
    (dgKernelRightAdjointCompositeIso R D E P) e
    (by
      change (R' ≫ dgNerve.map (dgModuleFunctorResolutionSource R C E F)) ≫
        dgKernelDerivedInfinity R D E P = _
      rw [hf]
      simp only [dgModuleResolvedSourceSectionEquivalence, Category.assoc]) he
    (dgUniversalRightAdjointCounit R T (SemifreeDGModules R E) G
      (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩))
  apply h₀.trans
  apply Eq.trans _ h₁.symm
  congr 1
  rw [QCatAdjunction.comp_counitHom]
  rw [dgModuleResolvedSourceSectionEquivalence_counitHom,
    dgUniversalRightAdjunction_counitHom]
  change _ = e.hom ≫ _
  rw [F2.functorIso_precomp_hom, F2.functorIso_postcomp_hom]
  rfl
end SerrePositivity.InfinityCategories
