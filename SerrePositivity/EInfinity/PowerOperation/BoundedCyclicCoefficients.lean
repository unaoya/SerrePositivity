module

public import SerrePositivity.EInfinity.PowerOperation.BoundedLinearHomQuasiIso
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# 上有界な作用付き係数の相対 Hom 関手

DAG XIII Construction 2.2.6 の完全入力の係数模型に使う。
上界の一様な選択を対象のデータに要求せず、二対象に共通の上界を取り、
証明済みの同じ周期 Hom が指定準同型を保つことを適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 上に有界な、同じ p 巡回群の作用付き係数複体。 -/
abbrev BoundedCyclicCoefficient :=
  ObjectProperty.FullSubcategory
    (fun M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ =>
      ∃ d : ℤ, M.IsStrictlyLE d)

/-- 同じ作用付き全複体への指定包含。 -/
abbrev boundedCyclicCoefficientInclusion : BoundedCyclicCoefficient p k ⥤
    CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ :=
  ObjectProperty.ι _

/-- 上有界係数についての同じ完全周期 Hom 関手。 -/
def boundedCyclicHomFunctor : BoundedCyclicCoefficient p k ⥤
    CochainComplex (ModuleCat.{u} k) ℤ :=
  boundedCyclicCoefficientInclusion p k ⋙ cyclicResolutionHomFunctor p k

/-- 上有界な二係数に共通の上界を取り、元の指定準同型を保つ。 -/
lemma boundedCyclicHomFunctor_map_quasiIso
    {M N : BoundedCyclicCoefficient p k} (f : M ⟶ N) [QuasiIso f.hom] :
    QuasiIso ((boundedCyclicHomFunctor p k).map f) := by
  obtain ⟨a, ha⟩ := M.property
  obtain ⟨b, hb⟩ := N.property
  have : M.obj.IsStrictlyLE a := ha
  have : N.obj.IsStrictlyLE b := hb
  have : M.obj.IsStrictlyLE (max a b) := M.obj.isStrictlyLE_of_le a _ (le_max_left _ _)
  have : N.obj.IsStrictlyLE (max a b) := N.obj.isStrictlyLE_of_le b _ (le_max_right _ _)
  exact cyclicResolutionHom_quasiIso_boundedAbove p f.hom (max a b)

/-- 元の係数の指定準同型を引き戻した相対射の類。 -/
def boundedCyclicCoefficientWeak : MorphismProperty (BoundedCyclicCoefficient p k) :=
  (HomologicalComplex.quasiIso (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) (.up ℤ)).inverseImage
    (boundedCyclicCoefficientInclusion p k)
deriving MorphismProperty.IsMultiplicative

/-- 同じ周期 Hom の相対関手。 -/
def boundedCyclicHomLocalizer : LocalizerMorphism (boundedCyclicCoefficientWeak p k)
    (HomologicalComplex.quasiIso (ModuleCat.{u} k) (.up ℤ)) where
  functor := boundedCyclicHomFunctor p k
  map _ _ f hf := by
    have : QuasiIso f.hom := (HomologicalComplex.mem_quasiIso_iff _).mp hf
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr
      (boundedCyclicHomFunctor_map_quasiIso p k f)

end SerrePositivity.EInfinity.PowerOperation
