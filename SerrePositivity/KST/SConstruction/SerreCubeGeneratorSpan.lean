module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorExt
public import Mathlib.LinearAlgebra.Quotient.Defs

/-! # 元の Serre cube の各次数の tensor 生成元による張り
概要：元の指定次数を持つ端点・辺 tensor 生成元は、元の次数加群全体を張る。
方針：元の生成元による線形射の判定を、同じ span による商写像へ適用する。
規約：元の加群と生成元を保持。使われ方：native HA の全生成元値からの線形射復元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の指定次数を持つ全 tensor 生成元の族。 -/
def serreCubeDegreeGenerator (n : ℕ) (k : ℤ)
    (i : {i : SerreCubeGeneratorIndex n // serreCubeGeneratorDegree n i = k}) :
    (serreCubeComplex A n).X k :=
  eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) i.property)
    (serreCubeGenerator A n i.val)

/-- 元の指定次数の全 tensor 生成元は、元の次数加群の全体を張る。 -/
lemma serreCubeDegreeGenerator_span (n : ℕ) (k : ℤ) :
    Submodule.span A (Set.range (serreCubeDegreeGenerator A n k)) = ⊤ := by
  let S := Submodule.span A (Set.range (serreCubeDegreeGenerator A n k))
  let V := ModuleCat.of A ((serreCubeComplex A n).X k ⧸ S)
  have hQ : (ModuleCat.ofHom S.mkQ : (serreCubeComplex A n).X k ⟶ V) = 0 := by
    apply serreCube_degree_hom_ext A n k
    intro i hi
    have hm : serreCubeDegreeGenerator A n k ⟨i, hi⟩ ∈ S :=
      Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero S).mpr hm
  apply top_unique
  intro w _
  have hz := ConcreteCategory.congr_hom hQ w
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

end SerrePositivity.KST.SConstruction
