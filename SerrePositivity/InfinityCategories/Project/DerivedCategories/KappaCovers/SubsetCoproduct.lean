module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DependencyPieces
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：依存閉な κ-small ラベル部分集合上の実余積図式は、全ラベルの余積を strict 余極限に持つ。
方針：各ラベルを含む部分集合を選び、共通上界でその選択からの独立性を示す。
規約：通常の余極限だけを主張する。native 普遍性は D-bar の別入力。
使われ方：D-8 d の自由 cell 層の strict 部分表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits
variable {A : Type u} (dep : A → Set A) {κ : Cardinal.{u}} [Fact κ.IsRegular]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] (L : A → C)

def dgKappaSubsetCoproduct : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaDependencyPieces dep (κ := κ) ⥤ C where
  obj s := ∐ (fun a : s.val => L a.val)
  map {s t} f := Sigma.desc (fun a => Sigma.ι (fun b : t.val => L b.val)
    ⟨a.val, leOfHom f a.property⟩)
  map_id s := by
    apply Sigma.hom_ext
    intro a
    simp only [Sigma.ι_comp_desc, Category.comp_id]
  map_comp f g := by
    apply Sigma.hom_ext
    intro a
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]

def dgKappaSubsetCoproductCocone : Cocone (dgKappaSubsetCoproduct dep (κ := κ) L) where
  pt := ∐ L
  ι.app s := Sigma.desc (fun a => Sigma.ι L a.val)
  ι.naturality s t f := by
    apply Sigma.hom_ext
    intro a
    simp only [dgKappaSubsetCoproduct, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      CategoryTheory.Functor.const_obj_map]
    exact (Category.comp_id _).symm

def dgKappaSubsetCoproductComponent (c : Cocone (dgKappaSubsetCoproduct dep (κ := κ) L))
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaDependencyPieces dep (κ := κ)) (a : s.val) : L a.val ⟶ c.pt :=
  Sigma.ι (fun b : s.val => L b.val) a ≫ c.ι.app s

omit [Fact κ.IsRegular] in
lemma dgKappaSubsetCoproductComponent_map (c : Cocone (dgKappaSubsetCoproduct dep (κ := κ) L))
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaDependencyPieces dep (κ := κ)} (f : s ⟶ t) (a : s.val) :
    dgKappaSubsetCoproductComponent dep L c t ⟨a.val, leOfHom f a.property⟩ =
      dgKappaSubsetCoproductComponent dep L c s a := by
  have h := congrArg (fun k => Sigma.ι (fun b : s.val => L b.val) a ≫ k) (c.w f)
  simpa only [dgKappaSubsetCoproduct, dgKappaSubsetCoproductComponent,
    Sigma.ι_comp_desc_assoc] using h

lemma dgKappaSubsetCoproductComponent_eq (c : Cocone (dgKappaSubsetCoproduct dep (κ := κ) L))
    (s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaDependencyPieces dep (κ := κ)) (a : A) (hs : a ∈ s.val) (ht : a ∈ t.val) :
    dgKappaSubsetCoproductComponent dep L c s ⟨a, hs⟩ =
      dgKappaSubsetCoproductComponent dep L c t ⟨a, ht⟩ := by
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaDependencyPieces_isCardinalFiltered dep (κ := κ)
  haveI := isFiltered_of_isCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaDependencyPieces dep (κ := κ)) κ
  exact (dgKappaSubsetCoproductComponent_map dep L c (IsFiltered.leftToMax s t) ⟨a, hs⟩).symm.trans
    (dgKappaSubsetCoproductComponent_map dep L c (IsFiltered.rightToMax s t) ⟨a, ht⟩)

/-- 各ラベルを被覆する同じ部分集合図式の strict 余極限の普遍性。 -/
def dgKappaSubsetCoproductIsColimit
    (hcover : ∀ a : A, ∃ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaDependencyPieces dep (κ := κ), a ∈ s.val) :
    IsColimit (dgKappaSubsetCoproductCocone dep (κ := κ) L) := by
  choose s hs using hcover
  refine {
    desc := fun c => Sigma.desc (fun a =>
      dgKappaSubsetCoproductComponent dep L c (s a) ⟨a, hs a⟩)
    fac := ?_
    uniq := ?_ }
  · intro c t
    apply Sigma.hom_ext
    intro a
    simpa only [dgKappaSubsetCoproductCocone, dgKappaSubsetCoproductComponent,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using
      dgKappaSubsetCoproductComponent_eq dep L c (s a.val) t a.val (hs a.val) a.property
  · intro c m hm
    apply Sigma.hom_ext
    intro a
    have h := congrArg (fun f => Sigma.ι (fun b : (s a).val => L b.val) ⟨a, hs a⟩ ≫ f) (hm (s a))
    simpa only [dgKappaSubsetCoproductCocone, dgKappaSubsetCoproductComponent,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
