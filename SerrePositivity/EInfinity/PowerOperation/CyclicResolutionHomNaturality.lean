module

public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionSingleHomology

/-!
# 離散係数の完全周期 Hom の全自然比較

DAG XIII Construction 2.2.6 の指定係数計算の補助。
同じ評価同値と零微分によるホモロジー比較を、全係数加群の射に対して自然にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (p : ℕ) [NeZero p] {k : Type u} [CommRing k] [CharP k p]

omit [CharP k p] in
/-- 同じ指定評価同値は、離散係数の全射の後合成と可換。 -/
lemma cyclicResolutionSingleDegreeEquiv_natural
    {A B : Rep.{u} k (PowerOperationCyclicGroup.{u} p)} [A.IsTrivial] [B.IsTrivial]
    (f : A ⟶ B) (i : ℤ)
    (z : Cochain (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A) i) :
    cyclicResolutionSingleDegreeEquiv p B i
      (z.comp (Cochain.ofHom
        ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).map f)) (add_zero i)) =
      f.hom (cyclicResolutionSingleDegreeEquiv p A i z) := by
  obtain ⟨a, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (by omega)
  rw [← Cochain.toSingleMk_postcomp]
  simp [cyclicResolutionSingleDegreeEquiv, Cochain.toSingleLinearEquiv,
    Cochain.toSingleEquiv, Cochain.toSingleMk]
  rfl

/-- ホモロジー比較は、同じ cycle の評価を保持する。 -/
lemma cyclicResolutionSingleHomologyIso_pi
    (A : Rep.{u} k (PowerOperationCyclicGroup.{u} p)) [A.IsTrivial] (i : ℤ) :
    (linearHomComplex k (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A)).homologyπ i ≫
      (cyclicResolutionSingleHomologyIso p A i).hom =
    (linearHomComplex k (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A)).iCycles i ≫
      (cyclicResolutionSingleDegreeEquiv p A i).toModuleIso.hom := by
  simp [cyclicResolutionSingleHomologyIso]

/-- 自明係数の全加群から同じ完全周期 Hom への全関手。 -/
def cyclicResolutionDiscreteCoefficientFunctor : ModuleCat.{u} k ⥤
    CochainComplex (ModuleCat.{u} k) ℤ :=
  Rep.trivialFunctor k (PowerOperationCyclicGroup.{u} p) ⋙
    singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0 ⋙
      cyclicResolutionHomFunctor p k

/-- 同じ離散係数 Hom のホモロジー比較は全表現射に自然。 -/
lemma cyclicResolutionSingleHomologyIso_natural
    {A B : Rep.{u} k (PowerOperationCyclicGroup.{u} p)} [A.IsTrivial] [B.IsTrivial]
    (f : A ⟶ B) (i : ℤ) :
    HomologicalComplex.homologyMap
      (linearHomComplexPostcompose k (powerOperationCompleteResolution p k)
        ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).map f)) i ≫
      (cyclicResolutionSingleHomologyIso p B i).hom =
      (cyclicResolutionSingleHomologyIso p A i).hom ≫ (forget₂ _ (ModuleCat k)).map f := by
  let K := linearHomComplex k (powerOperationCompleteResolution p k)
    ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A)
  rw [← cancel_epi (K.homologyπ i)]
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  dsimp only [K]
  rw [cyclicResolutionSingleHomologyIso_pi]
  simp only [← Category.assoc]
  rw [HomologicalComplex.cyclesMap_i, cyclicResolutionSingleHomologyIso_pi]
  simp only [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact cyclicResolutionSingleDegreeEquiv_natural p f i z

/-- 自明係数の完全周期 Hom の H^i は、全加群関手として元の係数と同型。 -/
def cyclicResolutionDiscreteHomologyNatIso (i : ℤ) :
    cyclicResolutionDiscreteCoefficientFunctor (k := k) p ⋙
      HomologicalComplex.homologyFunctor _ _ i ≅ 𝟭 (ModuleCat.{u} k) :=
  NatIso.ofComponents
    (fun A => cyclicResolutionSingleHomologyIso p
      ((Rep.trivialFunctor k (PowerOperationCyclicGroup.{u} p)).obj A) i)
    (fun f => cyclicResolutionSingleHomologyIso_natural p
      ((Rep.trivialFunctor k (PowerOperationCyclicGroup.{u} p)).map f) i)

end SerrePositivity.EInfinity.PowerOperation
