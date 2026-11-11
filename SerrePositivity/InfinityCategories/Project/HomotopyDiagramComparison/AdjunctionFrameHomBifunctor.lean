module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom

/-!
概要：随伴の frame Hom 同型を、独立した元の始域・終域パラメータに自然な二変数同型へ束ねる。
方針：同じ cosimplicial frame の左像と元の右像に通常の Hom 随伴を全次数で適用する。
規約：置換関手を任意の元の関手として保持。使われ方：cf 置換後の導来 Hom 随伴の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u vC vD vB wB vE wE
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type vC} [Category.{u} C] {D : Type vD} [Category.{u} D]
  {B : Type wB} [Category.{vB} B] {E : Type wE} [Category.{vE} E]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : B ⥤ (SimplexCategory ⥤ C)) (T : E ⥤ D)

/-- 元の frame の左像と元の終域置換からなる、実際の二変数 Hom。 -/
abbrev adjunctionLeftFrameHom : Bᵒᵖ ⥤ E ⥤ SSet.{u} :=
  (A ⋙ (Functor.whiskeringRight SimplexCategory C D).obj L).op ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft E D SSet.{u}).obj T

/-- 同じ元の frame と終域置換の右像からなる、実際の二変数 Hom。 -/
abbrev adjunctionRightFrameHom : Bᵒᵖ ⥤ E ⥤ SSet.{u} :=
  A.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft E C SSet.{u}).obj (T ⋙ R)

/-- 元の始域パラメータと終域パラメータの双方に自然な、全次数の Hom 随伴同型。 -/
def adjunctionFrameHomBifunctorIso :
    adjunctionLeftFrameHom (L := L) A T ≅ adjunctionRightFrameHom (R := R) A T :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse adj (A.obj X.unop)).app (T.obj Y))
      (by
        intro Y Y' f
        exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse adj (A.obj X.unop)).hom.naturality (T.map f)))
    (by
      intro X X' f
      ext Y n h
      exact adj.homEquiv_naturality_left ((A.map f.unop).app n.unop) h)

/-- この同型は、零単体だけでなく各次数で元の通常の Hom 随伴そのものを使う。 -/
lemma adjunctionFrameHomBifunctorIso_apply (X : Bᵒᵖ) (Y : E) (n : SimplexCategoryᵒᵖ)
    (f : L.obj ((A.obj X.unop).obj n.unop) ⟶ T.obj Y) :
    (((adjunctionFrameHomBifunctorIso adj A T).hom.app X).app Y).app n f =
      adj.homEquiv ((A.obj X.unop).obj n.unop) (T.obj Y) f := rfl

/-- 元の augmentation による普通の射の全次数の像も、同じ随伴の像と厳密に両立する。 -/
lemma adjunctionFrameHomBifunctorIso_augmentation (X : Bᵒᵖ) (Y : E) {Z : C}
    (a : A.obj X.unop ⟶ (Functor.const SimplexCategory).obj Z)
    (f : L.obj Z ⟶ T.obj Y) (n : SimplexCategoryᵒᵖ) :
    (((adjunctionFrameHomBifunctorIso adj A T).hom.app X).app Y).app n
        (L.map (a.app n.unop) ≫ f) =
      a.app n.unop ≫ adj.homEquiv Z (T.obj Y) f := by
  rw [adjunctionFrameHomBifunctorIso_apply]
  exact adj.homEquiv_naturality_left (a.app n.unop) f

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
