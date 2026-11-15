module
public import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeBasisEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion

/-! # 完備導来テンソルの係数三角形

## 概要
BS 著者版 Proposition 10.4 の逆方向と Lemma 10.5 の係数三角形を与える。

## 方針
半自由代表を用いて係数の短完全列から完備導来圏の三角形を作る。
核との完備テンソルが零なら、商環による作用を各コホモロジーへ移す。

## 規約
複体の有界性は仮定しない。コホモロジー次数を使う。

## 使われ方
一般の完備複体に対する almost 零性の判定。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.DifferentialGraded _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived
open scoped _root_.Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private theorem complexSemifree_kFlat {P : Complex R} (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R P) :
    complexKFlat R P :=
  moduleSemifree_objectwiseKFlat R PUnit.{1} (fun _ _ ↦ complexKFlat_unit R) hP PUnit.unit

private def completedModuleTensorUnresolvedIso (p : ℕ) (N : ModuleCat.{u} R) (M : DVertex R) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨completedModuleTensor p R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex R N) M⟩) ≅
    (derivedComplexCompletionFunctor R (p : R)).obj
      (DerivedCategory.Q.obj ((moduleTensorCochainFunctor (M.obj 0).val).obj N)) := by
  let P := (M.obj 0).val
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation_quasiIso R N
  have := complexKFlat_quasiIso_left R (complexSemifree_kFlat (M.obj 0).property)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation R N)
  exact e.counitIso.app _ ≪≫ (derivedComplexCompletionFunctor R (p : R)).mapIso
    (asIso (DerivedCategory.Q.map (cochainTensorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation R N) (𝟙 P))) ≪≫
      DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso N P))

/-- 完備導来テンソルの左入力に、古典的な商の perfectoid 化の核を置く。 -/
abbrev kernelTensor (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
    (hR : IsIntegralPerfectoid R p) (J : Ideal R) (M : DVertex R) : DVertex R :=
  completedModuleTensor p R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex R (ModuleCat.of R (perfectoidKernel p R hR J))) M

end SerrePositivity.BhattScholze.Almost


namespace SerrePositivity.BhattScholze.Almost
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.DifferentialGraded _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived
open scoped _root_.Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (J : Ideal R)

/-- 完備導来テンソルの左入力に古典的な perfectoid 商を置く。 -/
abbrev quotientTensor (M : DVertex R) : DVertex R :=
  completedModuleTensor p R
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex R (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R J p hR))) M

/-- 頂点の連結性は通常の導来圏の t 構造で判定できる。 -/
theorem isConnectiveAt_iff_isLE (n : ℤ) (M : DVertex R) :
    SerrePositivity.DerivedInfinity.IsConnectiveAt R n M ↔
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩).IsLE n := by
  rw [DerivedCategory.isLE_iff]
  exact forall_congr' (fun _ ↦ imp_congr_right (fun _ ↦ ModuleCat.isZero_iff_subsingleton.symm))

/-- 離散加群の頂点は零次より上のコホモロジーを持たない。 -/
theorem isLE_moduleHeartVertex (N : ModuleCat.{u} R) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex R N⟩).IsLE 0 := by
  let e := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartDerivedIso R).app N
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 商との完備テンソルの各コホモロジーは商環上の加群になる。 -/
theorem quotientTensor_isAlmostZero (M : DVertex R) :
    _root_.SerrePositivity.BhattScholze.Almost.IsAlmostZeroComplex p R hR J (quotientTensor p hR J M) := by
  let B := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R J p hR
  let q := quotientPerfdMap p R hR J
  let P := (M.obj 0).val
  let F := derivedComplexCompletionFunctor R (p : R)
  let X := DerivedCategory.Q.obj (baseChange q P)
  let iso := (derivedRestrictScalarsFactors q).app (baseChange q P) ≪≫
    DerivedCategory.Q.mapIso (restrictedBaseChangeComplexIso q P ≪≫
      cochainTensorSingleLeftIso (ModuleCat.of R B) P)
  let eB := completedModuleTensorUnresolvedIso p (ModuleCat.of R B) M ≪≫
    (F.mapIso iso).symm ≪≫ (derivedCompletionRestrictionIso q (p : R)).app X
  intro i
  let h := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eB ≪≫
    (derivedRestrictScalarsHomologyIso q i).app _
  apply SerrePositivity.Almost.IsAlmostZero.of_equiv h.toLinearEquiv.symm
  apply SerrePositivity.Almost.IsAlmostZero.iff_smul_eq_zero.mpr
  intro r hr x
  let y : (DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((derivedComplexCompletionFunctor B (q (p : R))).obj X) := x
  change q r • y = 0
  rw [show q r = 0 from hr, zero_smul]

private theorem exists_quotientTensorTriangle (M : DVertex R) (hM : SerrePositivity.DerivedInfinity.IsPComplete p R M) :
    ∃ T : Triangle (ConcreteDerivedCategory R), T ∈ distTriang _ ∧
      Nonempty (T.obj₁ ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj
        ⟨kernelTensor p R hR J M⟩) ∧
      Nonempty (T.obj₂ ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩) ∧
      Nonempty (T.obj₃ ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj
        ⟨quotientTensor p hR J M⟩) := by
  let K := perfectoidKernel p R hR J
  let B := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R J p hR
  let P := (M.obj 0).val
  let F := derivedComplexCompletionFunctor R (p : R)
  let S := ModuleCat.shortComplexOfCompEqZero K.subtype K.mkQ
    (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ K) K.injective_subtype K.mkQ_surjective
  obtain ⟨basis⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_nonempty_basis (M.obj 0).property
  have hflat (i : ℤ) : Module.Flat R (P.X i) := by
    let := Module.Free.of_basis (basis.basis i)
    infer_instance
  have hs := moduleTensorCochain_shortExact P hflat S hS
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hs)
  let e : (R ⧸ K) ≃ₐ[R] B :=
    { RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J) with
      commutes' := fun _ ↦ rfl }
  refine ⟨T, F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs),
    ⟨(completedModuleTensorUnresolvedIso p (ModuleCat.of R K) M).symm⟩, ?_, ?_⟩
  · exact ⟨F.mapIso (DerivedCategory.Q.mapIso (moduleTensorCochainUnitIso P)) ≪≫
      F.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedVertexLocalizationIso M).symm ≪≫
        (derivedComplexCompletionUnitIso R (p : R) _ hM).symm⟩
  · exact ⟨F.mapIso (DerivedCategory.Q.mapIso
        ((moduleTensorCochainFunctor P).mapIso e.toLinearEquiv.toModuleIso)) ≪≫
      (completedModuleTensorUnresolvedIso p (ModuleCat.of R B) M).symm⟩

/-- 核との完備テンソルが連結なら、元の複体は almost 連結になる。 -/
theorem almostConnective_of_kernelTensor_connective (M : DVertex R)
    (hM : SerrePositivity.DerivedInfinity.IsPComplete p R M) (hK : SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 (kernelTensor p R hR J M)) :
    IsAlmostConnective p R hR J M := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_quotientTensorTriangle p hR J M hM
  intro i hi
  let H := DerivedCategory.homologyFunctor (ModuleCat R) i
  have h₁ : IsZero (H.obj T.obj₁) :=
    (ModuleCat.isZero_iff_subsingleton.mpr (hK i hi)).of_iso (H.mapIso e₁)
  have hmono : Mono (H.map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
      (h₁.eq_of_src _ _)
  let f := (H.mapIso e₂).inv ≫ H.map T.mor₂ ≫ (H.mapIso e₃).hom
  have hf : Mono f := by dsimp [f]; infer_instance
  exact SerrePositivity.Almost.IsAlmostZero.of_injective f.hom
    ((ModuleCat.mono_iff_injective f).mp hf) (quotientTensor_isAlmostZero p hR J M i)

/-- 核と商で得る二つの完備テンソルから元の複体の連結性を復元する。 -/
theorem connective_of_kernelTensor_and_quotientTensor (M : DVertex R)
    (hM : SerrePositivity.DerivedInfinity.IsPComplete p R M) (hK : SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 (kernelTensor p R hR J M))
    (hB : SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 (quotientTensor p hR J M)) :
    SerrePositivity.DerivedInfinity.IsConnectiveAt R 0 M := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_quotientTensorTriangle p hR J M hM
  have h₁ := (isConnectiveAt_iff_isLE 0 _).mp hK
  have h₃ := (isConnectiveAt_iff_isLE 0 _).mp hB
  have h₁' : T.obj₁.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e₁.symm 0
  have h₃' : T.obj₃.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e₃.symm 0
  have h₂ := DerivedCategory.TStructure.t.isLE₂ T hT 0 h₁' h₃'
  exact (isConnectiveAt_iff_isLE 0 M).mpr
    (DerivedCategory.TStructure.t.isLE_of_iso e₂ 0)

/-- BS 著者版 Proposition 10.4 の逆方向。核との完備テンソルの零性から almost 零性を得る。 -/
theorem isAlmostZero_of_completedTensor_isZero (M : DVertex R)
    (hM : SerrePositivity.DerivedInfinity.IsPComplete p R M)
    (hz : IsZero ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨kernelTensor p R hR J M⟩)) :
    _root_.SerrePositivity.BhattScholze.Almost.IsAlmostZeroComplex p R hR J M := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_quotientTensorTriangle p hR J M hM
  have := (T.isZero₁_iff_isIso₂ hT).mp (hz.of_iso e₁)
  let e := e₂.symm ≪≫ asIso T.mor₂ ≪≫ e₃
  intro i
  let h := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e
  exact SerrePositivity.Almost.IsAlmostZero.of_equiv h.toLinearEquiv.symm
    (quotientTensor_isAlmostZero p hR J M i)

end SerrePositivity.BhattScholze.Almost

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 10.4" (partial := special) "一般の J で必要な同値（almost 零 ⇔ J_perfd との完備テンソルが 0）は証明済み。後半の圏同値は作らない（D66） ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Almost.isAlmostZero_of_completedTensor_isZero
