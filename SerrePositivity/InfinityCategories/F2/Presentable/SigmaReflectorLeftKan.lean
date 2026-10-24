module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaRepresentableColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafElementsLeftKan
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：全前層圏から P_Σ への専用左 Kan 延長の存在。
方針：各 Yoneda comma を元の小さい elements 図式へ戻す。
規約：一般 Bousfield 局所化や P_Σ 全体の余完備性を仮定しない。
使われ方：包含の左随伴となる反映 L の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {C : SSet.{u}} [Quasicategory C]

/-- 概要：全前層の elements 比較は元の左 Kan 射影を保つ。
方針：引き戻し交換の射影公式を元の密度比較へ合成する。
規約：同じ前層と小さい elements を保持する。
使われ方：専用反映の局所左 Kan 図式の存在。 -/
lemma presheafElementsLeftKanComparison_projection
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    presheafElementsLeftKanComparison F ≫
      leftKanProjection (yonedaInfinityMap C) (functorVertex F) =
      (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection F) := by
  dsimp only [presheafElementsLeftKanComparison, leftKanProjection]
  rw [Category.assoc]
  erw [pullbackSymmetry_inv_comp_fst]
  exact presheafElementsYonedaSliceComparison_projection F

/-- 概要：全前層の各 Yoneda comma に沿う P_Σ 値局所図式は余極限を持つ。
方針：同じ elements 比較で表現可能小図式の余極限を戻す。
規約：局所対象に限定せず、全前層頂点を量化する。
使われ方：全前層圏からの coherent な反映の存在入力。 -/
lemma sigmaReflectorLeftKanDiagram_hasColimit
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (v : (PresheafInfinity C) _⦋0⦌) :
    HasColimit (leftKanDiagram (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) v) := by
  obtain ⟨F, rfl⟩ := (presheafInfinityObjectEquiv C).surjective v
  change HasColimit (leftKanDiagram (yonedaInfinityMap C) (sigmaYonedaInfinityMap C)
    (functorVertex F))
  apply hasColimit_of_equivalentRestriction (presheafElementsLeftKanComparison F)
    (presheafElementsLeftKanComparison_isQCatEquivalence F)
  rw [leftKanDiagram, ← Category.assoc, presheafElementsLeftKanComparison_projection]
  exact sigmaYoneda_smallDiagram_hasColimit hC (smallRightUnstraighteningProjection F)

/-- 概要：P_Σ Yoneda を全前層圏へ左 Kan 延長する全関手が存在する。
方針：全ての前層頂点の局所余極限を元の存在定理へ渡す。
規約：元の Yoneda と指定単位の全自然性を保持する。
使われ方：専用反映 L の候補。 -/
lemma sigma_exists_reflectorLeftKan
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p) :
    ∃ (L : PresheafInfinity C ⟶ SigmaPresheafInfinity C)
      (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L)),
      IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ _
    (sigmaReflectorLeftKanDiagram_hasColimit hC)

end SerrePositivity.InfinityCategories.F2.Presentable
