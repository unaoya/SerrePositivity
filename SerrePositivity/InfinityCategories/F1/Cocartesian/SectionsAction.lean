module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeComposition
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSections

/-!
概要：元の cocartesian 関手の全相対 Hom は、同じ底の cocartesian section 空間へ作用する。
方針：元の相対豊穣合成を section 条件と cocartesian 辺の保存条件に制限する。
規約：対象ごとの後合成だけではなく、全高次パラメーターの実際の作用を構成する。
使われ方：cocartesian fibrations から QCat 値の section 評価への豊穣関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- section の各辺の cocartesian 性は、cocartesian 辺を保つ元の関手との合成で保たれる。 -/
lemma kanIsCocartesianSection_comp {B : SSet.{u}} (a p q : Over B)
    (v : (relativeFunctorSpace p.hom a.hom) _⦋0⦌)
    (w : (relativeFunctorSpace q.hom p.hom) _⦋0⦌)
    (hv : KanIsCocartesianSection p.hom a.hom v)
    (hw : cocartesianRelativeFunctorPredicate p.hom q.hom w) :
    KanIsCocartesianSection q.hom a.hom
      ((relativeFunctorComposition a p q).app (Opposite.op ⦋0⦌) (v, w)) := by
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex p.hom a.hom v
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex q.hom p.hom w
  rw [relativeFunctorComposition_vertex]
  simp only [KanIsCocartesianSection, kanRelativeFunctorOfVertex_vertex] at hv ⊢
  have hgw := (cocartesianRelativeFunctorPredicate_vertex _ _ _ _).mp hw
  intro e
  exact hgw _ (hv e)

/-- 同じ元の相対合成により、cocartesian 関手の全パラメーターを section へ作用させる。 -/
def cocartesianSectionsAction {B : SSet.{u}} (a p q : Over B) :
    kanCocartesianSections p.hom a.hom ⊗ cocartesianRelativeFunctorSpace p.hom q.hom ⟶
      kanCocartesianSections q.hom a.hom :=
  fullSubcomplexLift _
    ((kanCocartesianSectionsι p.hom a.hom ⊗ₘ
      cocartesianRelativeFunctorInclusion p.hom q.hom) ≫ relativeFunctorComposition a p q) (by
      intro s
      exact kanIsCocartesianSection_comp a p q s.1.val s.2.val
        (kanCocartesianSections_vertex _ _ s.1) (fullSubcomplexOnVertices_vertex s.2))

/-- section への作用は、元の相対関手空間への包含後には元の相対合成そのもの。 -/
lemma cocartesianSectionsAction_ι {B : SSet.{u}} (a p q : Over B) :
    cocartesianSectionsAction a p q ≫ kanCocartesianSectionsι q.hom a.hom =
      (kanCocartesianSectionsι p.hom a.hom ⊗ₘ
        cocartesianRelativeFunctorInclusion p.hom q.hom) ≫ relativeFunctorComposition a p q := rfl

/-- section への作用は、同じ元の cocartesian 恒等射を厳密な単位として保つ。 -/
lemma cocartesianSectionsAction_id {B : SSet.{u}} (a p : Over B) :
    (ρ_ (kanCocartesianSections p.hom a.hom)).inv ≫
      _ ◁ cocartesianRelativeFunctorIdentity p ≫ cocartesianSectionsAction a p p = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n s.val) (relativeFunctorComposition_id a p)

/-- 二つの同じ cocartesian 関手の相対合成は、section の二段階の作用と厳密に一致する。 -/
lemma cocartesianSectionsAction_assoc {B : SSet.{u}} (a p q r : Over B) :
    (α_ (kanCocartesianSections p.hom a.hom)
      (cocartesianRelativeFunctorSpace p.hom q.hom)
      (cocartesianRelativeFunctorSpace q.hom r.hom)).inv ≫
      cocartesianSectionsAction a p q ▷ _ ≫ cocartesianSectionsAction a q r =
    _ ◁ cocartesianRelativeFunctorComposition p q r ≫ cocartesianSectionsAction a p r := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, f, g⟩
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n (s.val, f.val, g.val))
    (relativeFunctorComposition_assoc a p q r)

end SerrePositivity.InfinityCategories
