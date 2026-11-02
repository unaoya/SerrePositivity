module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ThickeningSelfHomComparison

/-!
概要：最後の対象の指定後合成を二回行う操作は、元の合成射による一回の操作と一致する。
方針：全 Hom を元の同じ対象で正規化し、後合成の厳密合成則を適用する。
規約：比較同型の選択を加えない。使われ方：二固定射の高次 prism の共通面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (s : (SimplicialNerve C) _⦋n + 1⦌) {Y Z : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y) (h : Y ⟶ Z)
local notation "s₁" => coherentSimplexLastPost s g
local notation "h'" => eqToHom (coherentSimplexLastPost_last s g) ≫ h
local notation "s₂" => coherentSimplexLastPost s₁ h'
local notation "s₃" => coherentSimplexLastPost s (g ≫ h)

/-- 二回の指定後合成と合成射の後合成は、全対象で厳密に一致する。 -/
lemma coherentSimplexLastPost_comp_obj (i : Fin (n + 2)) :
    (s₂).obj ⟨ULift.up i⟩ = (s₃).obj ⟨ULift.up i⟩ := by
  induction i using Fin.lastCases <;>
    simp only [coherentSimplexLastPost, coherentSimplexLastPostObj,
      Fin.lastCases_last, Fin.lastCases_castSucc]

/-- 二回の指定後合成は元の合成射の後合成と、全 Hom の作用まで厳密に一致する。 -/
lemma coherentSimplexLastPost_comp : s₂ = s₃ := by
  apply EnrichedFunctor.ext SSet (fun i => coherentSimplexLastPost_comp_obj s g h i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change coherentSimplexLastPostHom s₁ h' i j ≫ eqToHom _ =
    coherentSimplexLastPostHom s (g ≫ h) i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    exact thickeningSelfHom_comparison s₂ s₃ ⟨ULift.up (Fin.last (n + 1))⟩
      (coherentSimplexLastPost_comp_obj s g h (Fin.last (n + 1)))
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (P.obj 0)
    change n + 1 ≤ j.val at hp
    have hj : j.val < n + 1 := j.isLt
    omega
  case cast.cast i j =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentSimplexLastPostObj_cast s (Y := Z) i)
      (coherentSimplexLastPostObj_cast s (Y := Z) j)))).1
    have e := congrArg (fun k => k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentSimplexLastPostObj_cast s (Y := Y) i)
      (coherentSimplexLastPostObj_cast s (Y := Y) j)))
      (coherentSimplexLastPostHom_cast_cast s₁ h' i j)
    change (_ ≫ _) ≫ _ = coherentSimplexLastPostHom s g i.castSucc j.castSucc ≫ _ at e
    rw [coherentSimplexLastPostHom_cast_cast s g i j] at e
    have r := coherentSimplexLastPostHom_cast_cast s (g ≫ h) i j
    simpa only [Category.assoc, eqToHom_trans] using e.trans r.symm
  case cast.last i =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentSimplexLastPostObj_cast s (Y := Z) i)
      (coherentSimplexLastPostObj_last s (Y := Z))))).1
    have e := congrArg (fun k => k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentSimplexLastPostObj_cast s (Y := Y) i) (rfl : Z = Z)))
      (coherentSimplexLastPostHom_cast_last s₁ h' i)
    simp only [Category.assoc] at e
    erw [simplicialHom_postcomp_display (coherentSimplexLastPostObj_cast s (Y := Y) i)
      (coherentSimplexLastPost_last s g) h, ← Category.assoc] at e
    have a := congrArg (fun k => k ≫
      eHomWhiskerLeft SSet (s.obj ⟨ULift.up i.castSucc⟩) h)
      (coherentSimplexLastPostHom_cast_last s g i)
    simp only [Category.assoc] at a
    have e' := e.trans a
    have r := coherentSimplexLastPostHom_cast_last s (g ≫ h) i
    simp only [Category.assoc, ← eHomWhiskerLeft_comp] at e'
    simpa only [Category.assoc, eqToHom_trans] using e'.trans r.symm

end SerrePositivity.InfinityCategories.F2
