module
public import SerrePositivity.KST.SConstruction.MultiSQuasicategoryEnrichedFunctor
public import SerrePositivity.KST.SConstruction.SExactQuasicategoryDiagram

/-! # 全高次比較を持つ元の有限反復 S• 図式
概要：全方向の元の多単体制限を、全完全関手族に自然な比較として束ねる。
方針：先頭方向の比較と残りの方向の S_n 像の自然性を帰納的に合成する。
規約：元の多単体図式の射をそのまま使う。使われ方：反復 core S• の厳密豊穣化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

private lemma parameterizedSquare_comp {X X' X'' Y Y' Y'' P : SSet.{u}}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
    (a : X ⊗ P ⟶ Y) (b : X' ⊗ P ⟶ Y') (c : X'' ⊗ P ⟶ Y'')
    (h : (f ▷ P) ≫ b = a ≫ g) (h' : (f' ▷ P) ≫ c = b ≫ g') :
    ((f ≫ f') ▷ P) ≫ c = a ≫ (g ≫ g') := by
  rw [comp_whiskerRight, Category.assoc, h', ← Category.assoc, h, Category.assoc]

/-- 全方向の元の多単体制限は、全高次の完全関手族に自然である。 -/
lemma multiSQuasicategoryEnrichedRestriction_naturality (r : ℕ)
    {d e : Fin r → SimplexCategoryᵒᵖ} (θ : d ⟶ e) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    ((multiSExactRestriction r θ C).hom ▷ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})) ≫
        uncurry ((multiSQuasicategoryEnrichedFunctor r e).map C D) =
      uncurry ((multiSQuasicategoryEnrichedFunctor r d).map C D) ≫
        (multiSExactRestriction r θ D).hom := by
  induction r with
  | zero =>
    change (𝟙 C.obj ▷ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι = uncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι ≫ 𝟙 D.obj
    rw [id_whiskerRight, Category.id_comp, Category.comp_id]
  | succ r ih =>
    have hi := sExactParameterizedNaturality (e 0).unop.len
      (multiSExactEnrichedMap r (fun i => d i.succ) C D)
      (multiSExactEnrichedMap r (fun i => e i.succ) C D)
      (multiSExactRestriction r (fun i => θ i.succ) C)
      (multiSExactRestriction r (fun i => θ i.succ) D)
      (ih (fun i => θ i.succ))
    have ho := ((sExactQuasicategoryRestriction (θ 0).unop.toOrderHom).precompose
      (multiSExactEnrichedEndofunctor r (fun i => d i.succ))).property C D
    rw [multiSExactRestriction_succ, multiSExactRestriction_succ,
      multiSQuasicategoryEnrichedFunctor_map_succ,
      multiSQuasicategoryEnrichedFunctor_map_succ]
    exact parameterizedSquare_comp _ _ _ _ _ _ _ ho hi

/-- 同じ元の全方向の制限を、全高次 Hom に自然な比較として保持する。 -/
def multiSQuasicategoryEnrichedRestriction (r : ℕ)
    {d e : Fin r → SimplexCategoryᵒᵖ} (θ : d ⟶ e) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (multiSQuasicategoryEnrichedFunctor.{u} r d)
      (multiSQuasicategoryEnrichedFunctor r e) :=
  ⟨fun C => (multiSExactRestriction r θ C).hom,
    multiSQuasicategoryEnrichedRestriction_naturality r θ⟩

/-- 元の全多単体作用を全高次比較の圏に束ねた、有限反復 S• 図式。 -/
def multiSQuasicategoryEnrichedDiagram (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  obj := multiSQuasicategoryEnrichedFunctor r
  map := multiSQuasicategoryEnrichedRestriction r
  map_id d := by
    apply Subtype.ext
    funext C
    exact congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (multiSExactRestriction_id r d C)
  map_comp θ φ := by
    apply Subtype.ext
    funext C
    exact congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom (multiSExactRestriction_comp r θ φ C)

end SerrePositivity.KST.SConstruction
