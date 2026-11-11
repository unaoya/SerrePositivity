module

public import SerrePositivity.KST.LocalizingInvariants.FinalHornMissingVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismLastContraction

/-!
概要：最終外ホーンを最後の頂点へ収縮し、末尾二点上の垂直辺を保持する。
方針：標準単体の最後の頂点への prism は欠けた頂点を増やさないのでホーンに制限する。
規約：収縮の零端は恒等。使われ方：cartesian 辺の充填を正方形族へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def finalHornLastVertex (n : ℕ) : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n _ _⟩

def finalHornPenultimateVertex (n : ℕ) : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm ((Fin.last (n + 1)).castSucc), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n _ _⟩

def finalHornLastContraction (n : ℕ) :
    (Δ[1] : SSet.{u}) ⊗ (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶
      (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) :=
  Subcomplex.lift ((Δ[1] ◁ (horn (n + 2) (Fin.last (n + 2))).ι) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 2)) (by
      rintro ⟨⟨d⟩⟩ _ ⟨⟨t, s⟩, rfl⟩
      rw [mem_horn_iff_notMem_range]
      obtain ⟨j, hj, hjr⟩ := (mem_horn_iff_notMem_range s.val (Fin.last (n + 2))).mp s.property
      refine ⟨j, hj, ?_⟩
      rintro ⟨k, hk⟩
      change (if t k = 0 then s.val k else Fin.last (n + 2)) = j at hk
      split_ifs at hk
      · exact hjr ⟨k, hk⟩
      · exact hj hk.symm)

lemma finalHornLastContraction_inclusion (n : ℕ) :
    finalHornLastContraction.{u} n ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      (Δ[1] ◁ (horn (n + 2) (Fin.last (n + 2))).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 2) := rfl

lemma finalHornLastContraction_zero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ≫
      finalHornLastContraction n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro k
  rfl

lemma finalHornLastContraction_one (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ≫
      finalHornLastContraction n = SSet.const (finalHornLastVertex n) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro k
  rfl

lemma finalHornLastContraction_penultimate_edge (n : ℕ) :
    (finalHornLastContraction n).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (finalHornPenultimateVertex n) 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma finalHornLastContraction_last_edge (n : ℕ) :
    (finalHornLastContraction n).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (finalHornLastVertex n) 1) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (finalHornLastVertex n) 1 := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

end SerrePositivity.KST.LocalizingInvariants
