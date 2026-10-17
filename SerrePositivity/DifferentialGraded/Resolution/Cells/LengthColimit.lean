module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.LengthSplit

/-! # path長filtrationの網羅性と最終HomのK-flat性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

omit [Small.{u} I] in
lemma mem_lengthSet_self (w : List I) : w ∈ lengthSet I w.length := Nat.le_refl _

def lengthDiagram (x y : D) : ℕ ⥤ Complex A where
  obj n := C.lengthHom A D I n x y
  map f := C.lengthMap A D I _ _ (leOfHom f) x y
  map_id n := C.lengthMap_self A D I n x y
  map_comp f g := (C.lengthMap_comp A D I _ _ _ (leOfHom f) (leOfHom g) x y).symm

def lengthCocone (x y : D) : Cocone (C.lengthDiagram A D I x y) where
  pt := C.attachedHom A D I x y
  ι :=
    { app := fun n => C.lengthHomInclusion A D I n x y
      naturality := fun m n f => by
        change C.lengthMap A D I m n (leOfHom f) x y ≫ C.lengthHomInclusion A D I n x y =
          C.lengthHomInclusion A D I m x y ≫ 𝟙 _
        rw [Category.comp_id, lengthMap_inclusion] }

lemma lengthMap_ι (m n : ℕ) (h : m ≤ n) (x y : D) (w : lengthSet I m) :
    Sigma.ι (fun w : lengthSet I m => C.term A D I w.val x y) w ≫
      C.lengthInternalMap A D I m n x y =
    Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) ⟨w.val, w.property.trans h⟩ :=
  ComplexCoproduct.ι_select_mem (fun w => C.term A D I w x y)
    (lengthSet I m) (lengthSet I n) w (w.property.trans h)

def lengthEvalIsColimit (x y : D) (i : ℤ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapCocone
      (C.lengthCocone A D I x y)) := by
  let H : IsColimit (Cofan.mk ((C.internalHom A D I x y).X i)
      (fun w : List I => (C.inclusion A D I w x y).f i)) :=
    isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : List I => C.term A D I w x y)
  let inc (w : List I) : (C.term A D I w x y).X i ⟶ (C.lengthInternalHom A D I w.length x y).X i :=
    (Sigma.ι (fun w : lengthSet I w.length => C.term A D I w.val x y)
      ⟨w, mem_lengthSet_self I w⟩).f i
  let leg (s : Cocone (C.lengthDiagram A D I x y ⋙
      HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) (n : ℕ) :
      (C.lengthInternalHom A D I n x y).X i ⟶ s.pt := s.ι.app n
  have hfac (s : Cocone (C.lengthDiagram A D I x y ⋙
      HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) (w : List I) :
      (C.inclusion A D I w x y).f i ≫
        H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length)) =
      inc w ≫ leg s w.length := H.fac _ ⟨w⟩
  refine
    { desc := fun s => H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length))
      fac := ?_
      uniq := ?_ }
  · intro s n
    apply (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : lengthSet I n => C.term A D I w.val x y)).hom_ext
    intro w
    change (Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w.as).f i ≫
      (C.lengthInclusion A D I n x y).f i ≫
        H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length)) =
      (Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w.as).f i ≫ leg s n
    have hp : Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w.as ≫
        C.lengthInclusion A D I n x y = C.inclusion A D I w.as.val x y :=
      ComplexCoproduct.ι_inclusion (fun w => C.term A D I w x y) (lengthSet I n) w.as
    rw [← Category.assoc, ← HomologicalComplex.comp_f, hp, hfac]
    have hs := s.w (homOfLE w.as.property)
    change (C.lengthInternalMap A D I w.as.val.length n x y).f i ≫ leg s n =
      leg s w.as.val.length at hs
    rw [← hs, ← Category.assoc, ← HomologicalComplex.comp_f]
    exact congrArg (fun f => f.f i ≫ leg s n)
      (C.lengthMap_ι A D I w.as.val.length n w.as.property x y
        ⟨w.as.val, mem_lengthSet_self I w.as.val⟩)
  · intro s m hm
    let m' : (C.internalHom A D I x y).X i ⟶ s.pt := m
    change m' = H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length))
    apply H.hom_ext
    intro w
    have hn := congrArg (fun f => inc w.as ≫ f) (hm w.as.length)
    change inc w.as ≫ (C.lengthInclusion A D I w.as.length x y).f i ≫ m' =
      inc w.as ≫ leg s w.as.length at hn
    have hi := congrArg (fun f => f.f i)
      (ComplexCoproduct.ι_inclusion (fun w => C.term A D I w x y)
        (lengthSet I w.as.length) ⟨w.as, mem_lengthSet_self I w.as⟩)
    change inc w.as ≫ (C.lengthInclusion A D I w.as.length x y).f i =
      (C.inclusion A D I w.as x y).f i at hi
    rw [← Category.assoc, hi] at hn
    change (C.inclusion A D I w.as x y).f i ≫ m' =
      (C.inclusion A D I w.as x y).f i ≫
        H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length))
    rw [hfac]
    exact hn

def lengthIsColimit (x y : D) : IsColimit (C.lengthCocone A D I x y) :=
  HomologicalComplex.isColimitOfEval _ _ (C.lengthEvalIsColimit A D I x y)

/-- 追加微分後の最終Homは、path長filtrationとexactな逐次余極限によりK-flat。 -/
lemma attachedHom_kFlat (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.attachedHom A D I x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have h := complexKFlat_colimit A (C.lengthDiagram A D I x y)
    (fun n => C.lengthHom_kFlat A D I hD n x y)
  exact complexKFlat_of_iso A
    ((colimit.isColimit _).coconePointUniqueUpToIso (C.lengthIsColimit A D I x y)).symm h

lemma attachedDGCategory_localHomKFlat (hD : localHomKFlat A D) :
    localHomKFlat A (C.Objects A D I) :=
  fun x y => C.attachedHom_kFlat A D I hD x.val y.val

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
