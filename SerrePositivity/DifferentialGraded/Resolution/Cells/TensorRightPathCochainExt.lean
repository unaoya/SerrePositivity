module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundarySquare

/-! # 任意次数cellの全合成の微分整合性：TensorRightPathCochainExt -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma tensorRightPathCochain_ext (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y ⊗ K) T p)
    (h : ∀ w : List I, (Cochain.ofHom (C.inclusion A D I w x y ▷ K)).comp f (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y ▷ K)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorRightCoproductIsColimit K (fun w : List I => C.term A D I w x y))).hom_ext
  rintro ⟨w⟩
  change (C.inclusion A D I w x y ▷ K).f i ≫ f.v i n hn =
    (C.inclusion A D I w x y ▷ K).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (C.term A D I w x y ⊗ K) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
