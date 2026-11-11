module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.NativeSimplexLift
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCriterion
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.QuotientNative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanEquivalenceLiftingFibration

/-!
概要：固定 ε の全成分へ持ち上げた候補から、実際の dg nerve 単体を回収する。
方針：D の ε Hom 包含の次数別単射性で、元関手圏の単体方程式を反映する。
規約：候補成分の ε 整合は未供給。これは入力 native 作用の存在宣言ではない。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) (D : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (S : Set C) (T : Set D)

/-- D の Hom 包含は全ての斉次次数で単射である。 -/
lemma quotientEpsilonForget_degree_injective
    (F G : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) (k : ℤ) :
    Function.Injective (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T).map F G).f k) := by
  change Function.Injective ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G).f k)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- 任意次数の候補成分の所属を、D の disk パラメータの ε 整合で判定する。 -/
lemma quotientEpsilonElement_factor_iff
    (F G : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) (k : ℤ)
    (z : (dgFunctorHom R C D F.val G.val).X k) :
    (∃ v : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G).X k,
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G).f k v = z) ↔
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonCompatible R C D S T F G
      ((_root_.SerrePositivity.DifferentialGraded.complexDiskHomEquiv R (dgFunctorHom R C D F.val G.val) k).symm z) := by
  constructor
  · rintro ⟨v, hv⟩
    apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom_factor_iff R C D S T F G _).mp
    refine ⟨(complexDiskHomEquiv R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G) k).symm v, ?_⟩
    apply (_root_.SerrePositivity.DifferentialGraded.complexDiskHomEquiv R (dgFunctorHom R C D F.val G.val) k).injective
    rw [_root_.SerrePositivity.DifferentialGraded.complexDiskHomEquiv_naturality]
    simpa only [Equiv.apply_symm_apply] using hv
  · intro hε
    obtain ⟨ρ, hρ⟩ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom_factor_iff R C D S T F G _).mpr hε
    refine ⟨complexDiskHomEquiv R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G) k ρ, ?_⟩
    rw [← _root_.SerrePositivity.DifferentialGraded.complexDiskHomEquiv_naturality, hρ]
    exact Equiv.apply_symm_apply _ z

/-- 元関手圏の既知の単体へ写る ε 成分族を、そのまま ε 関手圏の単体にする。 -/
def quotientEpsilonSimplexLift {n : ℕ}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R C D) n)
    (h : s.toSimplexData = t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) n :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgNerveSimplexOfMappedData (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T)
    (quotientEpsilonForget_degree_injective R C D S T) t s h

lemma quotientEpsilonSimplexLift_data {n : ℕ}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R C D) n)
    (h : s.toSimplexData = t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T)) :
    (quotientEpsilonSimplexLift R C D S T t s h).toSimplexData = t :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgNerveSimplexOfMappedData_data _ _ t s h

lemma quotientEpsilonSimplexLift_forget {n : ℕ}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R C D) n)
    (h : s.toSimplexData = t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T)) :
    (quotientEpsilonSimplexLift R C D S T t s h).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T) = s :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgNerveSimplexOfMappedData_map _ _ t s h

section NerveLift
variable (C' D' : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C'] [Small.{u} C']
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D'] [Small.{u} D'] (S' : Set C') (T' : Set D')

/-- 全成分の ε 持ち上げがあれば、方程式・単体的自然性を自動的に回収する。 -/
def quotientEpsilonNerveLift {X : SSet.{max u v}}
    (f : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R C' D'))
    (hlift : ∀ (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)),
      ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C' D' S' T') n,
        (f.app (Opposite.op ⦋n⦌) x).toSimplexData =
          t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T')) :
    X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C' D' S' T') :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgNerveMapLift (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T')
    (by
      intro F G h
      change F.val = G.val at h
      cases F
      cases G
      cases h
      rfl) (quotientEpsilonForget_degree_injective R C' D' S' T') f
    (fun n x => by
      obtain ⟨t, ht⟩ := hlift n x
      exact ⟨quotientEpsilonSimplexLift R C' D' S' T' t _ ht,
        quotientEpsilonSimplexLift_forget R C' D' S' T' t _ ht⟩)

/-- 元の全単体作用との比較は、頂点・辺だけでなく単体的写像全体の等号。 -/
lemma quotientEpsilonNerveLift_forget {X : SSet.{max u v}}
    (f : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R C' D'))
    (hlift : ∀ (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)),
      ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C' D' S' T') n,
        (f.app (Opposite.op ⦋n⦌) x).toSimplexData =
          t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T')) :
    quotientEpsilonNerveLift R C' D' S' T' f hlift ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T') = f :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgNerveMapLift_map _ _ _ _ _
/-- Kan な入力では、全単体成分の持ち上げから ε native core への射を得る。 -/
def quotientEpsilonCoreLift {X : SSet.{max u v}} [SSet.KanComplex X]
    (f : X ⟶ KST.SConstruction.dgFunctorNativeMappingSpace R C' D')
    (hlift : ∀ (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)),
      ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C' D' S' T') n,
        (f.app (Opposite.op ⦋n⦌) x).val.toSimplexData =
          t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T')) :
    X ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientEpsilonNativeCore R C' D' S' T' :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreIsoOfKan X).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
    (quotientEpsilonNerveLift R C' D' S' T'
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R C' D'))).ι) hlift)

/-- core への持ち上げも、元の作用と全単体で厳密に交換する。 -/
lemma quotientEpsilonCoreLift_forget {X : SSet.{max u v}} [SSet.KanComplex X]
    (f : X ⟶ KST.SConstruction.dgFunctorNativeMappingSpace R C' D')
    (hlift : ∀ (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)),
      ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C' D' S' T') n,
        (f.app (Opposite.op ⦋n⦌) x).val.toSimplexData =
          t.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T')) :
    quotientEpsilonCoreLift R C' D' S' T' f hlift ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientNativeInputForget R C' D' S' T' = f := by
  ext n x
  apply Subtype.ext
  change ((quotientEpsilonNerveLift R C' D' S' T'
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R C' D'))).ι) hlift ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C' D' S' T')).app n) x = _
  have h := quotientEpsilonNerveLift_forget R C' D' S' T'
    (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R C' D'))).ι) hlift
  have hn := NatTrans.congr_app h n
  exact ConcreteCategory.congr_hom hn x

end NerveLift

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
