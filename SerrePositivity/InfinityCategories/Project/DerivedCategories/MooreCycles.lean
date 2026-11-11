module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModuleSphereGroup
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Moore cycles と境界商

概要：全ての面が零の単体による境界商は Mathlib の Moore ホモロジーそのものである。
方針：正規化の共通核と cycles を線形同値で同定し、入射微分の像を比較する。
規約：正次数 n+1。使われ方：π と実際の Moore ホモロジーの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] (W : SimplicialObject (ModuleCat.{v} S))

/-- 概要：Moore 微分が零であることは零番目の面が零であることと同値。
方針：正規化部分対象の包含の単射性と微分の包含公式を使う。
規約：全ての chain 次数。使われ方：cycles の線形比較。 -/
lemma moore_d_zero_iff_face_zero (n : ℕ)
    (t : ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).X (n + 1)) :
    (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d (n + 1) n) t = 0 ↔
      W.δ 0 (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 1)).hom t).val) = 0 := by
  have h := congrArg (fun f => f t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernel_d_arrow W n)
  change (NormalizedMooreComplex.objX W n).arrow
    ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d (n + 1) n) t) =
      W.δ 0 (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 1)).hom t).val) at h
  have hinj := (ModuleCat.mono_iff_injective (NormalizedMooreComplex.objX W n).arrow).1
    inferInstance
  constructor
  · intro ht
    rw [ht, map_zero] at h
    exact h.symm
  · intro ht
    apply hinj
    rw [h, ht, map_zero]

/-- 概要：Moore cycles と全ての面が零の元の線形同値。
方針：共通核の具体的模型を取り、零番目の面を微分の核へ対応させる。
規約：正次数 n+1。使われ方：ホモロジー商の比較。 -/
def mooreCyclesSphereEquiv (n : ℕ) :
    LinearMap.ker ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d (n + 1) n).hom) ≃ₗ[S]
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n := by
  let E := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 1)).toLinearEquiv
  let fromSphere (z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W (n + 1) :=
    ⟨z.val, (Submodule.mem_iInf _).2 (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_face W z j.succ)⟩
  let L : LinearMap.ker
      ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d (n + 1) n).hom) →ₗ[S]
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n :=
    { toFun := fun s => ⟨(E s.val).val, (Submodule.mem_iInf _).2 (fun j => by
        by_cases hj : j = 0
        · subst j
          exact (moore_d_zero_iff_face_zero W n s.val).1 s.property
        · have he : (j.pred hj).succ = j := Fin.succ_pred j hj
          rw [← he]
          exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreKernelModule_face W (E s.val) (j.pred hj))⟩
      map_add' := by
        intro s t
        apply Subtype.ext
        change (E (s.val + t.val)).val = (E s.val).val + (E t.val).val
        rw [map_add]
        rfl
      map_smul' := by
        intro r s
        apply Subtype.ext
        change (E (r • s.val)).val = r • (E s.val).val
        rw [map_smul]
        rfl }
  apply LinearEquiv.ofBijective L
  constructor
  · intro s t h
    have hv : (E s.val).val = (E t.val).val :=
      congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n => z.val) h
    exact Subtype.ext (E.injective (Subtype.ext hv))
  · intro z
    have hz : E.symm (fromSphere z) ∈ LinearMap.ker
        ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d (n + 1) n).hom) := by
      apply (moore_d_zero_iff_face_zero W n _).2
      change W.δ 0 ((E (E.symm (fromSphere z))).val) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_face W z 0
    refine ⟨⟨E.symm (fromSphere z), hz⟩, Subtype.ext ?_⟩
    change (E (E.symm (fromSphere z))).val = z.val
    rw [LinearEquiv.apply_symm_apply]

/-- 概要：Moore cycles の比較は入射微分を零番目の面へ送る。
方針：Moore 微分と包含の公式を一つ上の次数で評価する。
規約：抽象的 short complex の toCycles を用いる。使われ方：境界の像の比較。 -/
lemma mooreCyclesSphereEquiv_boundary (n : ℕ)
    (t : ((normalizedMooreComplex (ModuleCat.{v} S)).obj W).X (n + 2)) :
    mooreCyclesSphereEquiv W n
      ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).sc'
        (n + 2) (n + 1) n).moduleCatToCycles t) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereBoundaryMap W n ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 2)).hom t) := by
  apply Subtype.ext
  change (NormalizedMooreComplex.objX W (n + 1)).arrow
    ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).d (n + 2) (n + 1)) t) =
      W.δ 0 ((NormalizedMooreComplex.objX W (n + 2)).arrow t)
  exact congrArg (fun f => f t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernel_d_arrow W (n + 1))

/-- 概要：Moore 境界の像は球面単体側の境界の像と一致する。
方針：微分の比較と各項の同型の全射性を使う。
規約：線形部分加群の等式。使われ方：商加群の同型。 -/
lemma mooreCyclesSphereEquiv_range (n : ℕ) :
    (LinearMap.range
      ((((normalizedMooreComplex (ModuleCat.{v} S)).obj W).sc'
        (n + 2) (n + 1) n).moduleCatToCycles)).map
        (mooreCyclesSphereEquiv W n).toLinearMap = LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereBoundaryMap W n) := by
  ext z
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 2)).hom t, (mooreCyclesSphereEquiv_boundary W n t).symm⟩
  · rintro ⟨u, rfl⟩
    let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 2)).inv u
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    apply (mooreCyclesSphereEquiv_boundary W n t).trans
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereBoundaryMap W n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelIso W (n + 2)).toLinearEquiv.apply_symm_apply u)

/-- 概要：Mathlib の Moore ホモロジーは球面単体の Moore 境界商と線形同型である。
方針：short complex の具体的な核・像商と cycles の線形同値を合成する。
規約：正次数 n+1。使われ方：π と Moore ホモロジーの比較の終域。 -/
def mooreHomologySphereIso (n : ℕ) :
    (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homology (n + 1)) ≅
      ModuleCat.of S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereHomologyQuotient W n) :=
  (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homologyIsoSc'
    (n + 2) (n + 1) n (by simp) (by simp)) ≪≫
    (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).sc'
      (n + 2) (n + 1) n).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ _ (mooreCyclesSphereEquiv W n)
      (mooreCyclesSphereEquiv_range W n)).toModuleIso

end SerrePositivity.InfinityCategories.Project.DerivedCategories
