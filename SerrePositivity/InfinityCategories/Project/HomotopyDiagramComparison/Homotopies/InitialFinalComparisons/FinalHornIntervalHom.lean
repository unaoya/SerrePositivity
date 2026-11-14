module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornKnownIntervals
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceIntervalRestriction

/-!
概要：最終外側ホーンの既知区間で、元の Hom と単位・合成・面制限を回収する。
方針：区間外の既知面から作った豊穣関手を同じ Path Hom へ移す。
規約：未知二区間の Hom を仮定しない。使われ方：外側ホーンの合成面の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 既知閉区間の回収関手から、元の両端の Path Hom 写像を取り出す。 -/
def finalHornKnownIntervalHom (a b : Fin (n + 3)) (hab : a ≤ b)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalFunctor σ a b hp)
    ⟨ULift.up a, le_rfl, hab⟩ ⟨ULift.up b, hab, le_rfl⟩

/-- 同じ既知 Hom 回収は、区間外の任意の既知面の区間 Hom に一致する。 -/
lemma finalHornKnownIntervalHom_eq_interval (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b)
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) (hout : j < a ∨ b < j) :
    finalHornKnownIntervalHom σ a b hab hp = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom σ j hj a b hout
      ⟨ULift.up.{u} a, le_rfl, hab⟩ ⟨ULift.up.{u} b, hab, le_rfl⟩ := by
  let x : Set.Icc (ULift.up.{u} a) (ULift.up.{u} b) := ⟨ULift.up a, le_rfl, hab⟩
  let y : Set.Icc (ULift.up.{u} a) (ULift.up.{u} b) := ⟨ULift.up b, hab, le_rfl⟩
  have hm (F G : EnrichedFunctor SSet
      (SimplicialThickening (Set.Icc (ULift.up.{u} a) (ULift.up.{u} b))) C) (h : F = G) :
      HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap F x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap G x y) := by
    subst G
    rfl
  exact eq_of_heq (hm _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalFunctor_eq_viaFace σ a b hp j hj hout))

/-- 同じ既知 Hom 回収は、任意の区間外の既知面からの直接回収に一致。 -/
lemma finalHornKnownIntervalHom_eq_viaFace (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b)
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) (hout : j < a ∨ b < j) :
    finalHornKnownIntervalHom σ a b hab hp = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalVertex_ne_outside j a b hout ⟨ULift.up.{u} a, le_rfl, hab⟩)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalVertex_ne_outside j a b hout ⟨ULift.up.{u} b, hab, le_rfl⟩) :=
  (finalHornKnownIntervalHom_eq_interval σ a b hab hp j hj hout).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom_eq_viaFace σ j hj a b hout _ _)

/-- 大きい既知区間上の回収を小さい既知区間へ移すと、同じ標準回収に戻る。 -/
lemma finalHornKnownIntervalHom_on_subinterval (a b : Fin (n + 3))
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) (hout : j < a ∨ b < j)
    (x y : Set.Icc (ULift.up.{u} a) (ULift.up.{u} b)) (hxy : x ≤ y)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval x.val.down y.val.down) :
    finalHornKnownIntervalHom σ x.val.down y.val.down hxy hp =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom σ j hj a b hout x y := by
  have ho : j < x.val.down ∨ y.val.down < j := by
    rcases hout with hja | hbj
    · exact Or.inl (lt_of_lt_of_le hja x.property.1)
    · exact Or.inr (lt_of_le_of_lt y.property.2 hbj)
  rw [finalHornKnownIntervalHom_eq_viaFace σ x.val.down y.val.down hxy hp j hj ho,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom_eq_viaFace]

/-- 同じ既知 Hom 回収は元の単位を保つ。 -/
lemma finalHornKnownIntervalHom_id (a : Fin (n + 3)) (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a a) :
    eId SSet (SimplicialThickening.mk (ULift.up.{u} a)) ≫
      finalHornKnownIntervalHom σ a a le_rfl hp = eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.intervalHomMap_id (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornKnownIntervalFunctor σ a a hp) ⟨ULift.up a, le_rfl, le_rfl⟩

/-- 三つの区間が既知なら、同じ Hom 回収は元の合成を保つ。 -/
lemma finalHornKnownIntervalHom_comp (a b c : Fin (n + 3)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a b) (hpbc : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval b c)
    (hpac : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval a c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c) ≫
      finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac =
    (finalHornKnownIntervalHom σ a b hab hpab ⊗ₘ finalHornKnownIntervalHom σ b c hbc hpbc) ≫
      SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
  let x : Set.Icc (ULift.up.{u} a) (ULift.up.{u} c) := ⟨ULift.up a, le_rfl, hab.trans hbc⟩
  let y : Set.Icc (ULift.up.{u} a) (ULift.up.{u} c) := ⟨ULift.up b, hab, hbc⟩
  let z : Set.Icc (ULift.up.{u} a) (ULift.up.{u} c) := ⟨ULift.up c, hab.trans hbc, le_rfl⟩
  have go (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) (hout : j < a ∨ c < j) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c) ≫
        finalHornKnownIntervalHom σ a c (hab.trans hbc) hpac =
      (finalHornKnownIntervalHom σ a b hab hpab ⊗ₘ finalHornKnownIntervalHom σ b c hbc hpbc) ≫
        SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ c) := by
    rw [finalHornKnownIntervalHom_on_subinterval σ a c j hj hout x z (hab.trans hbc) hpac,
      finalHornKnownIntervalHom_on_subinterval σ a c j hj hout x y hab hpab,
      finalHornKnownIntervalHom_on_subinterval σ a c j hj hout y z hbc hpbc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornIntervalHom_comp σ j hj a c hout x y z
  by_cases ha : a = 0
  · exact go (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
      (Or.inr (hpac.resolve_left (fun h ↦ h ha)))
  · exact go 0 (ne_of_lt ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
      (Or.inl (lt_of_le_of_ne (Fin.zero_le a) (Ne.symm ha)))

/-- 既知 Hom 回収を元の任意の既知面へ制限すると、その面の元の Hom に戻る。 -/
lemma finalHornKnownIntervalHom_on_face (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2))
    (a b : Fin (n + 2)) (hab : a ≤ b)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornKnownInterval (j.succAbove a) (j.succAbove b)) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
      ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      finalHornKnownIntervalHom σ (j.succAbove a) (j.succAbove b)
        ((Fin.strictMono_succAbove j).monotone hab) hp =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face (Fin.last (n + 2)) j hj) a b := by
  have go (k : Fin (n + 3)) (hk : k ≠ Fin.last (n + 2))
      (hout : k < j.succAbove a ∨ j.succAbove b < k) :
      (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
        ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
        finalHornKnownIntervalHom σ (j.succAbove a) (j.succAbove b)
          ((Fin.strictMono_succAbove j).monotone hab) hp =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face (Fin.last (n + 2)) j hj) a b := by
    rw [finalHornKnownIntervalHom_eq_viaFace σ (j.succAbove a) (j.succAbove b)
      ((Fin.strictMono_succAbove j).monotone hab) hp k hk hout]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face_of_outside σ j k hj hk a b hab hout
  by_cases ha : j.succAbove a = 0
  · exact go (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate n) (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n))
      (Or.inr (hp.resolve_left (fun h ↦ h ha)))
  · exact go 0 (ne_of_lt ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_pos n).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornPenultimate_lt_last n)))
      (Or.inl (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha)))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
