module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPost

/-!
概要：coherent 単体の最後に指定射を付け足し、元の全面を厳密に回収する。
方針：最後の頂点を退化で複製し、新しい最後の対象だけを指定射で後合成する。
規約：単体の次数は任意、局所 Kan 性・充填の選択は不要。
使われ方：二つの固定射を元の全係数 prism へ付け足す高次整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 最後の頂点の退化複製も、同じ元の最後の対象を持つ。 -/
lemma coherentSimplexLastDegenerate_last {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) :
    ((SimplicialNerve C).σ (Fin.last n) s).obj ⟨ULift.up (Fin.last (n + 1))⟩ =
      s.obj ⟨ULift.up (Fin.last n)⟩ := by
  change s.obj ⟨ULift.up ((Fin.last n).predAbove (Fin.last (n + 1)))⟩ = _
  rw [Fin.predAbove_right_last]

/-- 元の全面を変えず、同じ最後の対象から出る指定射を一辺追加する。 -/
def coherentSimplexAppendMorphism {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) {Y : C}
    (g : s.obj ⟨ULift.up (Fin.last n)⟩ ⟶ Y) : (SimplicialNerve C) _⦋n + 1⦌ :=
  coherentSimplexLastPost ((SimplicialNerve C).σ (Fin.last n) s)
    (eqToHom (coherentSimplexLastDegenerate_last s) ≫ g)

/-- 最後の対象の指定後合成は、最後を除いた面を厳密に保持する。 -/
lemma coherentSimplexLastPost_face_last {n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌)
    {Y : C} (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y) :
    (SimplicialNerve C).δ (Fin.last (n + 1)) (coherentSimplexLastPost s g) =
      (SimplicialNerve C).δ (Fin.last (n + 1)) s := by
  have h : (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom =
      (Fin.castSuccOrderEmb.toOrderHom : Fin (n + 1) →o Fin (n + 2)) := by
    apply OrderHom.ext
    apply funext
    intro i
    change (Fin.last (n + 1)).succAbove i = i.castSucc
    exact Fin.succAbove_last_apply i
  change (SimplicialThickening.functor
    (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom.uliftMap).comp SSet _ =
    (SimplicialThickening.functor
      (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom.uliftMap).comp SSet _
  rw [h]
  exact coherentSimplexLastPost_old_face s g

/-- 追加した最後の頂点を除くと、元の単体自身を全 Hom ごと回収する。 -/
lemma coherentSimplexAppendMorphism_face_last {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌)
    {Y : C} (g : s.obj ⟨ULift.up (Fin.last n)⟩ ⟶ Y) :
    (SimplicialNerve C).δ (Fin.last (n + 1)) (coherentSimplexAppendMorphism s g) = s := by
  rw [coherentSimplexAppendMorphism, coherentSimplexLastPost_face_last]
  exact ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_σ_succ (SimplicialNerve C) (i := Fin.last n)) s

/-- 付け足した最後の対象は指定射の終域。 -/
lemma coherentSimplexAppendMorphism_last {n : ℕ} (s : (SimplicialNerve C) _⦋n⦌)
    {Y : C} (g : s.obj ⟨ULift.up (Fin.last n)⟩ ⟶ Y) :
    (coherentSimplexAppendMorphism s g).obj ⟨ULift.up (Fin.last (n + 1))⟩ = Y :=
  coherentSimplexLastPost_last _ _

end SerrePositivity.InfinityCategories.F2
