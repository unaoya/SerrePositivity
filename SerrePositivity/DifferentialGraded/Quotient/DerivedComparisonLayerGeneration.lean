module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFreeGeneration
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerTriangle
public import SerrePositivity.DifferentialGraded.Verdier.DerivedCoproductComparison
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # 局所 K-flat 仮定による長さ層と有限長比較 cone の生成

正の path 項の生成性を、実際の加群直和の導来像と長さ filtration の各層へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCoproduct_finiteCellFactorTarget (S : Set D) {I : Type w} [Small.{u} I]
    (M : I → ModuleCategory A D)
    (hM : ∀ i, moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (M i))) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (∐ M)) :=
  (moduleFiniteCellFactorTarget A D S).prop_of_iso (moduleDerivedCoproductIso A D M)
    (moduleFiniteCellFactorTarget_coproduct_small A D _ hM)

/-- 同じ有限因子分解性は、厳密な加群図式の逐次余極限でも保たれる。 -/
lemma moduleSequentialColimit_finiteCellFactorTarget (S : Set D)
    (F : ℕ ⥤ ModuleCategory A D)
    (hF : ∀ n, moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (F.obj n)))
    (s : Cocone F) (hs : IsColimit s) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj s.pt) := by
  let R := sequentialCoproductFamily.{u} F
  have hR : moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (∐ R)) :=
    moduleCoproduct_finiteCellFactorTarget A D S R (fun i => hF i.down)
  have hc : moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    (moduleFiniteCellFactorTarget A D S).ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hR hR
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F s)
      (moduleSequentialConeDesc_quasiIso A D F s hs)) hc

lemma nonemptyPath_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (w : Word S) (hw : w ≠ []) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D w z))) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons b w => exact positivePath_finiteCellFactorTarget A D S h b w z

/-- 全ての正の固定長層の導来像は、S に関する有限因子分解性を持つ。 -/
lemma lengthLayerModule_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (z : D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (selectedPathModule A D S (fun w => w.length = n + 1) z)) := by
  apply moduleCoproduct_finiteCellFactorTarget A D S
    (fun w : LengthWord S (n + 1) => ForgetEnrichment.of (Complex A) (pathModule A D w.val z))
  intro w
  apply nonemptyPath_finiteCellFactorTarget A D S h w.val _ z
  intro hw
  have hh := w.property
  rw [hw, List.length_nil] at hh
  omega

lemma lengthLayerCone_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (z : D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (lengthModuleTransition A D S z (Nat.le_succ n)))) :=
  (moduleFiniteCellFactorTarget A D S).prop_of_iso (lengthLayerDerivedConeIso A D S z n).symm
    (lengthLayerModule_finiteCellFactorTarget A D S h z n)

lemma lengthModuleTransition_trW (S : Set D) (h : localKFlat A D S) (z : D) (n : ℕ) :
    (moduleFiniteCellFactorTarget A D S).trW
      ((moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.le_succ n))) :=
  ((moduleFiniteCellFactorTarget A D S).trW_iff_of_distinguished
    (lengthLayerDerivedTriangle A D S z n) (lengthLayerDerivedTriangle_distinguished A D S z n)).mpr
      (lengthLayerModule_finiteCellFactorTarget A D S h z n)

/-- 零段階から任意の有限長段階への比較は、同じ三角部分圏に関する分母となる。 -/
lemma lengthZeroToStage_trW (S : Set D) (h : localKFlat A D S) (z : D) (n : ℕ) :
    (moduleFiniteCellFactorTarget A D S).trW
      ((moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.zero_le n))) := by
  let P := moduleFiniteCellFactorTarget A D S
  let F := lengthModuleDiagram A D S z ⋙ moduleToDerived A D
  have hs (k : ℕ) : P.trW (F.map (homOfLE (Nat.le_succ k))) :=
    lengthModuleTransition_trW A D S h z k
  change P.trW (F.map (homOfLE (Nat.zero_le n)))
  induction n with
  | zero =>
    have he : homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_id]
    exact P.trW.id_mem _
  | succ n ih =>
    have he : homOfLE (Nat.zero_le n) ≫ homOfLE (Nat.le_succ n) =
        homOfLE (Nat.zero_le (n + 1)) := Subsingleton.elim _ _
    have ht := P.trW.comp_mem _ _ ih (hs n)
    rw [← CategoryTheory.Functor.map_comp, he] at ht
    exact ht

lemma lengthZeroToStageCone_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (z : D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (lengthModuleTransition A D S z (Nat.zero_le n)))) :=
  ((moduleFiniteCellFactorTarget A D S).trW_iff_of_distinguished
    (moduleDerivedConeTriangle A D (lengthModuleTransition A D S z (Nat.zero_le n)))
    (moduleDerivedConeTriangle_distinguished A D
      (lengthModuleTransition A D S z (Nat.zero_le n)))).mp
        (lengthZeroToStage_trW A D S h z n)

end SerrePositivity.DifferentialGraded.DGQuotient
