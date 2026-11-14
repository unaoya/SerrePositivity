module
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 一点 dg 環上での次数付き線形写像の自然性

概要：通常の次数付き線形写像は一点 dg 環の全次数作用と可換する。
方針：一点加群の Hom 複体の比較同型で任意の cochain を戻し、その自然性を使う。
規約：線形写像に chain map 条件は課さない。使われ方：filtration の次数付き分裂。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex Opposite
variable (S : Type u) [CommRing S]

/-- 概要：一点環上では任意の次数付き線形写像が全次数作用に関して自然である。
方針：Hom 複体の同型で degree 0 cochain を主 Hom end に戻す。
規約：微分との可換性は要求しない。使われ方：次数付き分裂の自然性。 -/
theorem ringGradedNaturality {P Q : Complex S} (a : ∀ k : ℤ, P.X k ⟶ Q.X k)
    (p i j : ℤ) (hij : i + p = j)
    (f : GradedHom S (op (PUnit.unit : PUnit.{1})) (op (PUnit.unit : PUnit.{1})) p) :
    moduleActionComponent S PUnit.{1}
        (ForgetEnrichment.of (Complex S) (ringModule S P)) PUnit.unit PUnit.unit p i j hij f ≫
        a j =
      a i ≫ moduleActionComponent S PUnit.{1}
        (ForgetEnrichment.of (Complex S) (ringModule S Q)) PUnit.unit PUnit.unit p i j hij f := by
  let e := ringModuleHomIso S (ringModule S P) (ringModule S Q)
  let z := e.inv.f 0 (Cochain.ofHoms a)
  have hz : (moduleHomπ S PUnit.{1} (ringModule S P) (ringModule S Q) PUnit.unit).f 0 z =
      Cochain.ofHoms a := by
    have h := congrArg (fun g => g.f 0 (Cochain.ofHoms a)) e.inv_hom_id
    exact h
  have h := moduleHomElement_naturality S PUnit.{1} 0 z (op PUnit.unit) (op PUnit.unit) p f
  rw [hz] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  have hv := Cochain.congr_v h i j (by omega)
  rw [Cochain.comp_v _ _ _ i j j hij (add_zero j),
    Cochain.comp_v _ _ _ i i j (add_zero i) hij] at hv
  change (((ringModule S P).map (op PUnit.unit) (op PUnit.unit)).f p f).v i j hij ≫
    a j = a i ≫ (((ringModule S Q).map (op PUnit.unit) (op PUnit.unit)).f p f).v i j hij
  simpa only [Cochain.ofHoms_v] using hv

/-- 概要：複体の射を明示的な一点加群の射へ戻す。
方針：一点評価の充満性で逆像を取る。
規約：対象は既存の `ringModule`。使われ方：次数付き分裂の転送。 -/
def ringComplexMap {P Q : Complex S} (f : P ⟶ Q) :
    ForgetEnrichment.of (Complex S) (ringModule S P) ⟶
      ForgetEnrichment.of (Complex S) (ringModule S Q) :=
  (moduleEvaluation S PUnit.{1} PUnit.unit).preimage f

/-- 概要：一点加群へ戻した射の評価は元の複体の射に一致する。
方針：充満忠実評価の逆像の法則を用いる。
規約：対象上の評価は定義的に恒等。使われ方：分裂の各法則の照合。 -/
theorem ringComplexMap_evaluation {P Q : Complex S} (f : P ⟶ Q) :
    (moduleEvaluation S PUnit.{1} PUnit.unit).map (ringComplexMap S f) = f :=
  Functor.map_preimage _ _

/-- 概要：通常の複体の次数付き分裂は一点 dg 加群の次数付き分裂を与える。
方針：評価で分裂の線形等式を照合し、任意の次数付き写像の自然性を使う。
規約：retraction と section に微分との可換性は課さない。
使われ方：semibasis の高さで切った段と自由商の分裂。 -/
def ringComplexGradedSplit {P Q R : Complex S} (f : P ⟶ Q) (g : Q ⟶ R)
    (r : ∀ k : ℤ, Q.X k ⟶ P.X k) (s : ∀ k : ℤ, R.X k ⟶ Q.X k)
    (hfr : ∀ k, f.f k ≫ r k = 𝟙 _) (hsg : ∀ k, s k ≫ g.f k = 𝟙 _)
    (hsr : ∀ k, s k ≫ r k = 0) (hfg : f ≫ g = 0)
    (hdecomp : ∀ k, r k ≫ f.f k + g.f k ≫ s k = 𝟙 _) :
    ModuleGradedSplit S PUnit.{1} (ringComplexMap S f) (ringComplexMap S g) where
  retraction _ := r
  section_ _ := s
  inclusion_retraction x k := by
    cases x
    rw [ringComplexMap_evaluation]
    exact hfr k
  section_projection x k := by
    cases x
    rw [ringComplexMap_evaluation]
    exact hsg k
  section_retraction _ k := hsr k
  inclusion_projection := by
    apply (moduleEvaluation S PUnit.{1} PUnit.unit).map_injective
    rw [Functor.map_comp, ringComplexMap_evaluation, ringComplexMap_evaluation,
      Functor.map_zero]
    exact hfg
  decomposition x k := by
    cases x
    rw [ringComplexMap_evaluation, ringComplexMap_evaluation]
    exact hdecomp k
  retraction_naturality x y p i j hij a := by
    cases x
    cases y
    exact ringGradedNaturality S r p i j hij a
  section_naturality x y p i j hij a := by
    cases x
    cases y
    exact (ringGradedNaturality S s p i j hij a).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
