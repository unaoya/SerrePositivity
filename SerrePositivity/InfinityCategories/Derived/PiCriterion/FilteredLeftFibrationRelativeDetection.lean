module

public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredLeftFibrationDetection

/-!
概要：filtered な底の全空間の有限な相対図式を同じ fiber の Kan 置換で検出する。
方針：境界を含む有限部分複体の共通段へ因子分解し、その全体を一つの fiber へ輸送する。
規約：輸送後の境界の等式と、元の境界・全体への実際のホモトピーを保持する。
使われ方：一般 coherent な filtered 図式での有限射と境界条件の同時検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：全空間模型への有限な射と元の境界を、一つの fiber へ同時に移せる。
方針：連続置換の相対因子分解と有限部分複体の fiber 輸送を合成する。
規約：境界は輸送後に厳密に一致し、元の両指定射へのホモトピーを返す。 -/
lemma continuousKanLeftFibration_finite_relative_detection {A K E B : SSet.{u}}
    [A.Finite] [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ K) (a : A ⟶ E)
    (f : K ⟶ continuousKanReplacement.obj E)
    (h : a ≫ continuousKanReplacementUnit.app E = i ≫ f) :
    ∃ b : B _⦋0⦌, ∃ t : A ⟶ vertexFiber p b,
      ∃ g : K ⟶ continuousKanReplacement.obj (vertexFiber p b),
        i ≫ g = t ≫ continuousKanReplacementUnit.app (vertexFiber p b) ∧
        Nonempty (SSet.Homotopy a (t ≫ vertexFiberι p b)) ∧
        Nonempty (SSet.Homotopy f (g ≫ continuousKanReplacement.map (vertexFiberι p b))) := by
  obtain ⟨j, a₀, ha₀⟩ := finiteSubcomplex_factorization a
  have hh : (a₀ ≫ continuousKanReplacementUnit.app j.val) ≫
      continuousKanReplacement.map j.val.ι = i ≫ f := by
    rw [Category.assoc, ← continuousKanReplacementUnit.naturality j.val.ι,
      CategoryTheory.Functor.id_map, ← Category.assoc, ha₀]
    exact h
  obtain ⟨k, v, r, hi, hr⟩ := finiteSubcomplex_relative_factorization_after_preserving_functor
    continuousKanReplacement E i j (a₀ ≫ continuousKanReplacementUnit.app j.val) f hh
  let v' := Subcomplex.homOfLE (leOfHom v)
  let a' := a₀ ≫ v'
  have ha' : a' ≫ k.val.ι = a := by
    dsimp only [a', v']
    rw [Category.assoc, Subcomplex.homOfLE_ι, ha₀]
  obtain ⟨b, s, ⟨H⟩⟩ := leftFibration_finite_fiber_detection p k.val.ι
  refine ⟨b, a' ≫ s, r ≫ continuousKanReplacement.map s, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hi, Category.assoc, Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← continuousKanReplacementUnit.naturality]
    simp only [CategoryTheory.Functor.id_map, a', v', Category.assoc]
  · have H' := functorHomotopyPrecomp H a'
    simpa only [← Category.assoc, ha'] using Nonempty.intro H'
  · obtain ⟨H'⟩ := continuousKanReplacement_map_homotopy H
    have H'' := functorHomotopyPrecomp H' r
    simpa only [CategoryTheory.Functor.map_comp, ← Category.assoc, hr] using Nonempty.intro H''

end SerrePositivity.InfinityCategories.F2
