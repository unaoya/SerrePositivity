module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SimultaneousFiberDetection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredLeftFibrationDetection

/-!
概要：同じ filtered な底の二つの全空間 Kan 模型への有限射を、共通頂点の元の二 fiber で表す。
方針：各有限射の fiber 表示を共通の頂点へ輸送し、元の比較ホモトピーと合成する。
規約：元の二射・元の fiber の値を保持する。
使われ方：一般 coherent filtered 余極限の有限積比較への有限射の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二つの全空間模型への有限射を同じ頂点の二 fiber で同時に表示する。
方針：各 fiber 検出を共通頂点へ輸送し、Kan 標的の実際のホモトピーを合成する。
規約：二つの有限形状は異なってよい。使われ方：有限積の比較の有限検査。 -/
lemma continuousKanLeftFibration_pair_finite_fiber_detection {K L E D B : SSet.{u}}
    [K.Finite] [L.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (f : K ⟶ continuousKanReplacement.obj E) (g : L ⟶ continuousKanReplacement.obj D) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ vertexFiber p b, ∃ t : L ⟶ vertexFiber q b,
      Nonempty (SSet.Homotopy f (s ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E)) ∧
      Nonempty (SSet.Homotopy g (t ≫ vertexFiberι q b ≫ continuousKanReplacementUnit.app D)) := by
  obtain ⟨b₀, a, ⟨Hf⟩⟩ :=
    continuousKanLeftFibration_finite_fiber_detection_unreplaced p f
  obtain ⟨b₁, v, ⟨Hg⟩⟩ :=
    continuousKanLeftFibration_finite_fiber_detection_unreplaced q g
  obtain ⟨b, s, t, ⟨Hs⟩, ⟨Ht⟩⟩ := leftFibration_pair_finite_fiber_detection p q
    (a ≫ vertexFiberι p b₀) (v ≫ vertexFiberι q b₁)
  have combine {A Z : SSet.{u}} [KanComplex Z] {r s t : A ⟶ Z}
      (H : SSet.Homotopy r s) (J : SSet.Homotopy s t) : Nonempty (SSet.Homotopy r t) :=
    (functorVertex_piZero_eq_iff_homotopy r t).mp
      (((functorVertex_piZero_eq_iff_homotopy r s).mpr ⟨H⟩).trans
        ((functorVertex_piZero_eq_iff_homotopy s t).mpr ⟨J⟩))
  have Hs' : SSet.Homotopy
      (a ≫ vertexFiberι p b₀ ≫ continuousKanReplacementUnit.app E)
      (s ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E) := by
    simpa only [Category.assoc] using
      functorHomotopyPostcomp Hs (continuousKanReplacementUnit.app E)
  have Ht' : SSet.Homotopy
      (v ≫ vertexFiberι q b₁ ≫ continuousKanReplacementUnit.app D)
      (t ≫ vertexFiberι q b ≫ continuousKanReplacementUnit.app D) := by
    simpa only [Category.assoc] using
      functorHomotopyPostcomp Ht (continuousKanReplacementUnit.app D)
  exact ⟨b, s, t, combine Hf Hs', combine Hg Ht'⟩

end SerrePositivity.InfinityCategories.F2
