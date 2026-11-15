module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeValueFrame

/-!
概要：評価の左随伴を、評価頂点に関して反変な関手に束ねる。
方針：自由図式の余積の添字を前合成で送り、全成分の一致で単位・合成則を証明する。
規約：既存の自由図式関手の対象と射をそのまま使う。
使われ方：HTT 4.2.4.4のRR02(a)、Hom要素圏上の自由frameの全族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape

/-- 評価頂点の射に沿う、同じ自由図式の反変な移送。 -/
def strictDiagramFreeAtReindex {i j : strictDiagramIndex d} (f : i ⟶ j) :
    strictDiagramFreeAt A d j ⟶ strictDiagramFreeAt A d i where
  app V :=
    { app := fun k => Sigma.desc (fun g => Sigma.ι (fun _ : i ⟶ k => V) (f ≫ g))
      naturality := by
        intro k l a
        apply Sigma.hom_ext
        intro g
        simp [strictDiagramFreeAt, Category.assoc] }
  naturality := by
    intro V W a
    apply NatTrans.ext
    funext k
    apply Sigma.hom_ext
    intro g
    simp [strictDiagramFreeAt, Category.assoc]

/-- 前合成の移送は恒等射を保つ。 -/
lemma strictDiagramFreeAtReindex_id (i : strictDiagramIndex d) :
    strictDiagramFreeAtReindex A d (𝟙 i) = 𝟙 (strictDiagramFreeAt A d i) := by
  apply NatTrans.ext
  funext V
  apply NatTrans.ext
  funext k
  apply Sigma.hom_ext
  intro g
  simp only [strictDiagramFreeAtReindex, NatTrans.id_app, Sigma.ι_desc, Category.id_comp]
  exact (Category.comp_id _).symm

/-- 前合成の移送は合成を反変に保つ。 -/
lemma strictDiagramFreeAtReindex_comp {i j k : strictDiagramIndex d}
    (f : i ⟶ j) (g : j ⟶ k) :
    strictDiagramFreeAtReindex A d (f ≫ g) =
      strictDiagramFreeAtReindex A d g ≫ strictDiagramFreeAtReindex A d f := by
  apply NatTrans.ext
  funext V
  apply NatTrans.ext
  funext l
  apply Sigma.hom_ext
  intro h
  simp [strictDiagramFreeAtReindex, Category.assoc]

/-- 評価頂点全体にわたる、指定した自由図式関手の反変な族。 -/
def strictDiagramFreeAtFunctor :
    (strictDiagramIndex d)ᵒᵖ ⥤ Complex A ⥤ StrictComplexDiagram A d where
  obj i := strictDiagramFreeAt A d i.unop
  map f := strictDiagramFreeAtReindex A d f.unop
  map_id i := strictDiagramFreeAtReindex_id A d i.unop
  map_comp f g := strictDiagramFreeAtReindex_comp A d g.unop f.unop

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
