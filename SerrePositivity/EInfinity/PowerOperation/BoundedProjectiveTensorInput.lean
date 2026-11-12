module

public import SerrePositivity.EInfinity.PowerOperation.BoundedCyclicCoefficients
public import SerrePositivity.EInfinity.PowerOperation.TensorPowerUpperBound
public import SerrePositivity.EInfinity.PowerOperation.TensorPowerRepresentationQuasiIso

/-!
# 上有界射影入力から同じ巡回係数模型への相対関手

DAG XIII Construction 2.2.6 の完全入力の前段。
同じ p 入力を上有界な係数に送り、元の準同型の保存を証明する。
完全入力に使える一般性を保ち、次数ごとの射影性と上界を明示する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 上有界かつ各項が射影的な、元の入力複体の全部分圏。 -/
abbrev BoundedProjectiveInput := ObjectProperty.FullSubcategory
  (fun K : Complex k => (∃ a : ℤ, K.IsStrictlyLE a) ∧ ∀ i, Projective (K.X i))

/-- 元の入力の全複体への指定包含。 -/
abbrev boundedProjectiveInputInclusion : BoundedProjectiveInput k ⥤ Complex k :=
  ObjectProperty.ι _

/-- 同じ符号付き p 入力を、上有界な巡回係数へ送る全関手。 -/
def boundedProjectiveTensorInputFunctor :
    BoundedProjectiveInput k ⥤ BoundedCyclicCoefficient p k :=
  ObjectProperty.lift _
    (boundedProjectiveInputInclusion k ⋙ powerOperationTensorInput p k) (fun K => by
      obtain ⟨a, ha⟩ := K.property.1
      have : K.obj.IsStrictlyLE a := ha
      exact ⟨p * a, tensorPowerRepresentation_isStrictlyLE K.obj p
        (powerOperationCyclicPermutation p) a⟩)

/-- 同じ指定 p 入力は、元の上有界射影入力の準同型を保つ。 -/
lemma boundedProjectiveTensorInputFunctor_map_quasiIso
    {M N : BoundedProjectiveInput k} (f : M ⟶ N) [QuasiIso f.hom] :
    QuasiIso ((boundedProjectiveTensorInputFunctor p k).map f).hom := by
  obtain ⟨a, ha⟩ := M.property.1
  obtain ⟨b, hb⟩ := N.property.1
  have : M.obj.IsStrictlyLE a := ha
  have : N.obj.IsStrictlyLE b := hb
  have (i : ℤ) : Projective (M.obj.X i) := M.property.2 i
  have (i : ℤ) : Projective (N.obj.X i) := N.property.2 i
  have : M.obj.IsKProjective := isKProjective_of_projective M.obj a
  have : N.obj.IsKProjective := isKProjective_of_projective N.obj b
  exact tensorPowerRepresentationFunctor_map_quasiIso f.hom p (powerOperationCyclicPermutation p)

/-- 元の射影入力の指定準同型の類。 -/
def boundedProjectiveInputWeak : MorphismProperty (BoundedProjectiveInput k) :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} k) (.up ℤ)).inverseImage
    (boundedProjectiveInputInclusion k)
deriving MorphismProperty.IsMultiplicative

/-- 同じ p 入力を保持する相対関手。 -/
def boundedProjectiveTensorInputLocalizer : LocalizerMorphism (boundedProjectiveInputWeak k)
    (boundedCyclicCoefficientWeak p k) where
  functor := boundedProjectiveTensorInputFunctor p k
  map _ _ f hf := by
    have : QuasiIso f.hom := (HomologicalComplex.mem_quasiIso_iff _).mp hf
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr
      (boundedProjectiveTensorInputFunctor_map_quasiIso p k f)

end SerrePositivity.EInfinity.PowerOperation
