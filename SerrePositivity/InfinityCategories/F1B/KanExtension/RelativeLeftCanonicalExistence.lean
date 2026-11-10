module

public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeFamilyDiagramEq
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCanonicalFamilyIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitImageIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaRelativeLocalReindex
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：標準底余錐上の局所相対余極限から元と標的を保つ左 Kan 延長を構成する。
方針：図式固定の底余錐の比較同型を持ち上げ、普遍底余錐上の局所存在へ移す。
規約：入力は通常の標準局所図式と標準底余錐を使う。
使われ方：Kerodon 7.3.6.7 の相対的な厳密な存在の局所仮定との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準底余錐上の局所相対余極限を普遍 comma 底余錐上へ移す。
方針：固定図式上の底余錐の同型を元の余錐の族へ持ち上げる。
規約：元の標準局所図式を変えず、新しい像を厳密に実現する。
使われ方：標準の局所存在仮定を既存の相対 join 組み立てへ渡す。 -/
lemma exists_kanRelativeLeftLocalColimit_over_universal {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U) (δ : K ⟶ C)
    (F₀ : K ⟶ D) (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀) (c : C _⦋0⦌)
    (z : JoinCocone (leftKanDiagram δ F₀ c)) (hz : IsRelativeColimitCone U z)
    (hzu : z.val ≫ U = (leftKanCanonicalCocone δ H₀ c).val) :
    ∃ d : JoinCocone (leftKanDiagram δ F₀ c), IsRelativeColimitCone U d ∧
      d.val ≫ U = joinMap (kanLeftKanShapeToCommaFiber δ c) (𝟙 (Δ[0] : SSet.{u})) ≫
        (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c
          (kanLeftCommaUniversalDiagram δ ≫ H₀)).val := by
  have he : leftKanDiagram δ (δ ≫ H₀) c = (leftKanDiagram δ F₀ c) ≫ U := by
    simp only [leftKanDiagram, Category.assoc, hFU]
  let a := SerrePositivity.InfinityCategories.F1B.coconeOfDiagramEq he (leftKanCanonicalCocone δ H₀ c)
  let b := SerrePositivity.InfinityCategories.F1B.coconeOfDiagramEq he (kanLeftCommaUniversalLocalCocone δ H₀ c)
  have ha : a = kanPostcomposeCocone U z := Subtype.ext hzu.symm
  have ei := SerrePositivity.InfinityCategories.F1B.coconeFamilyIsoOfDiagramEq he (kanLeftCommaCanonicalFamilyIso δ H₀ c)
  change VertexIso (coconeFamilyVertexEquiv _ a) (coconeFamilyVertexEquiv _ b) at ei
  rw [ha] at ei
  obtain ⟨d, hd, hdb⟩ := exists_kanRelativeColimit_over_iso_image
    (leftKanDiagram δ F₀ c) U hU z hz b ei.symm
  exact ⟨d, hd, hdb⟩

/-- 概要：標準局所余錐上の相対余極限から元と標的を厳密に保つ左 Kan 延長が存在する。
方針：各底余錐を固定図式の同型で普遍 comma 形へ移し、局所存在から厳密に組み立てる。
規約：元 F₀ と標的 H₀ を等式で保つ。底余錐は標準のものを入力する。
使われ方：一般の isofibration 上の元の相対左 Kan 制限の存在部分。 -/
@[kerodon 0302]
lemma exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits
    {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (F₀ : K ⟶ D) (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (leftKanDiagram δ F₀ c),
      IsRelativeColimitCone U z ∧ z.val ≫ U = (leftKanCanonicalCocone δ H₀ c).val) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧ G ≫ U = H₀ ∧
      IsRelativeLeftKanExtendedFrom U δ G := by
  apply exists_kanRelativeLeftCanonical_strict_extension_of_local_universal_colimits
    U hU δ hδ F₀ H₀ hFU
  intro c
  obtain ⟨z, hz, hzu⟩ := hlocal c
  exact exists_kanRelativeLeftLocalColimit_over_universal U hU δ F₀ H₀ hFU c z hz hzu

end SerrePositivity.InfinityCategories.F1B
