module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerDeformation

/-!
概要：指定 Verdier 下側二胞体の変形が、元の二つの短辺を全時刻で固定することを確認する。
方針：三頂点の連続する二点に値を持つ path の変形では、新しい頂点が加わらないことを使う。
規約：共有対角はこの固定条件に含めない。短辺の全単体の等号を保持する。
使われ方：K-6 c4 の上下三角柱を、同じ共有対角で貼るための外周境界条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SimplicialThickening SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem shortPath_deformation (n r : ℕ)
    (A : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
    (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
    (hlo : ∀ k, r ≤ (A k).down.val) (hhi : ∀ k, (A k).down.val ≤ r + 1)
    {i j : ULift.{u} (Fin (n + 1))} (P : SimplicialThickening.Path i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation A t P = (SimplicialThickening.functorMap A ⟨i⟩ ⟨j⟩).obj P := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ A '' P.I ∨ ∃ k ∈ P.I, t k = 1 ∧ A k ≤ z ∧ z ≤ A j) ↔ z ∈ A '' P.I
  constructor
  · rintro (hz | ⟨k, hk, _ht, hkz, hzj⟩)
    · exact hz
    · have hi := A.monotone (P.left_le k hk)
      have h₀ := hlo i
      have h₁ := hhi j
      have h₂ := hlo k
      have hcase : z.down.val = r ∨ z.down.val = r + 1 := by
        change (A k).down.val ≤ z.down.val at hkz
        change z.down.val ≤ (A j).down.val at hzj
        omega
      rcases hcase with hcase | hcase
      · refine ⟨i, P.left, ?_⟩
        apply ULift.ext
        apply Fin.ext
        change (A i).down.val ≤ (A k).down.val at hi
        change (A k).down.val ≤ z.down.val at hkz
        omega
      · refine ⟨j, P.right, ?_⟩
        apply ULift.ext
        apply Fin.ext
        change z.down.val ≤ (A j).down.val at hzj
        omega
  · exact Or.inl

private theorem shortPath_deformationEnriched (n r : ℕ)
    (A : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
    (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
    (hlo : ∀ k, r ≤ (A k).down.val) (hhi : ∀ k, (A k).down.val ≤ r + 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched A t = SimplicialThickening.functor A := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => shortPath_deformation n r A t hlo hhi (P.obj k))

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 下側の第一短辺は、同じ全一単体として全時刻固定される。 -/
theorem verdierFullSLowerDeformation_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (verdierFullSLowerDeformation d).h =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ stdSimplex.δ (2 : Fin 3) ≫
        SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched
    ((stdSimplex.δ (2 : Fin 3)).app _ a).down.toOrderHom.uliftMap
    (t.down.toOrderHom.comp ⟨ULift.down, fun _ _ h => h⟩)).comp SSet
      (verdierFullSLowerSimplex d) =
    (SimplicialThickening.functor
      ((stdSimplex.δ (2 : Fin 3)).app _ a).down.toOrderHom.uliftMap).comp SSet
      (verdierFullSLowerSimplex d)
  congr 1
  apply shortPath_deformationEnriched _ 0
  · intro k; exact Nat.zero_le _
  · intro k
    change (Fin.succAbove (2 : Fin 3) (a.down.toOrderHom k.down)).val ≤ 1
    generalize a.down.toOrderHom k.down = z
    fin_cases z <;> decide

/-- 下側の第二短辺は、同じ全一単体として全時刻固定される。 -/
theorem verdierFullSLowerDeformation_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (verdierFullSLowerDeformation d).h =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ stdSimplex.δ (0 : Fin 3) ≫
        SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched
    ((stdSimplex.δ (0 : Fin 3)).app _ a).down.toOrderHom.uliftMap
    (t.down.toOrderHom.comp ⟨ULift.down, fun _ _ h => h⟩)).comp SSet
      (verdierFullSLowerSimplex d) =
    (SimplicialThickening.functor
      ((stdSimplex.δ (0 : Fin 3)).app _ a).down.toOrderHom.uliftMap).comp SSet
      (verdierFullSLowerSimplex d)
  congr 1
  apply shortPath_deformationEnriched _ 1
  · intro k
    change 1 ≤ (Fin.succAbove (0 : Fin 3) (a.down.toOrderHom k.down)).val
    generalize a.down.toOrderHom k.down = z
    fin_cases z <;> decide
  · intro k
    exact Nat.le_of_lt_succ (Fin.is_lt _)

end SerrePositivity.KST.Fibration
