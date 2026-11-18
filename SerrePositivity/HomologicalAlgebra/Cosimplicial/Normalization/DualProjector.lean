module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Normalization.IntegerComplex
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Homology.Opposite

/-!
# 同じDold–Kan射影の余単体的交代複体への移送

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L21、報告 §399。
元の反対圏のPInftyと指定ホモトピーを、同じ交代余面複体へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory _root_.HomologicalComplex _root_.AlgebraicTopology _root_.Opposite
open scoped _root_.Simplicial _root_.DoldKan _root_.AlgebraicTopology.DoldKan
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 同じ余単体的対象を反対圏の単体的対象として読む（Dold–Kan）。 -/
def dualSimplicial : SimplicialObject ((ModuleCat.{u} A)ᵒᵖ) :=
  (cosimplicialSimplicialEquiv (ModuleCat A)).functor.obj (op X)

/-- 同じ交代複体の反対圏の次数・微分の比較（Dold–Kan）。 -/
def dualAlternatingIso :
    ((alternatingFaceMapComplex ((ModuleCat A)ᵒᵖ)).obj (_root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).unop ≅
      (alternatingCofaceMapComplex (ModuleCat A)).obj X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    change (AlternatingCofaceMapComplex.obj X).d i (i + 1) =
      ((AlternatingFaceMapComplex.obj (_root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).d (i + 1) i).unop
    dsimp only [AlternatingCofaceMapComplex.obj, AlternatingFaceMapComplex.obj]
    rw [CochainComplex.of_d, ChainComplex.of_d]
    exact AlternatingCofaceMapComplex.d_eq_unop_d X i)

/-- 元のPInftyを同じ交代余面複体へ移した射影（Dold–Kan）。 -/
def cofaceProjectorNat :
    (alternatingCofaceMapComplex (ModuleCat A)).obj X ⟶
      (alternatingCofaceMapComplex (ModuleCat A)).obj X :=
  (_root_.SerrePositivity.CosimplicialNormalization.dualAlternatingIso A X).inv ≫
    (HomologicalComplex.unopFunctor (ModuleCat A) (.down ℕ)).map
      (DoldKan.PInfty (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).op ≫ (_root_.SerrePositivity.CosimplicialNormalization.dualAlternatingIso A X).hom

/-- 移した射影の各次数は同じ元のPInftyの成分（Dold–Kan）。 -/
lemma cofaceProjectorNat_f (q : ℕ) :
    (_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X).f q = ((DoldKan.PInfty (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).f q).unop := by
  change 𝟙 _ ≫ ((DoldKan.PInfty (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).f q).unop ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- 同じ既存のPInftyから恒等へのホモトピーを運ぶ（Dold–Kan）。 -/
def cofaceProjectorNat_homotopy : Homotopy (_root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X) (𝟙 _) := by
  let U := HomologicalComplex.unopFunctor (ModuleCat A) (.down ℕ)
  let e := _root_.SerrePositivity.CosimplicialNormalization.dualAlternatingIso A X
  let Q := (alternatingFaceMapComplex ((ModuleCat A)ᵒᵖ)).obj (_root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)
  let h := (DoldKan.homotopyPInftyToId (_root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).unop
  have H := (h.compLeft e.inv).compRight e.hom
  have hi := U.map_id (op Q)
  have he := congrArg (fun f => e.inv ≫ f ≫ e.hom) hi
  have he' : e.inv ≫ U.map (𝟙 (op Q)) ≫ e.hom = 𝟙 _ :=
    he.trans ((congrArg (fun f => e.inv ≫ f) (Category.id_comp e.hom)).trans e.inv_hom_id)
  have heI : ((e.inv ≫ U.map (𝟙 Q).op) ≫ e.hom) = 𝟙 _ :=
    (congrArg (fun f => (e.inv ≫ U.map f) ≫ e.hom) (op_id (X := Q))).trans
      ((Category.assoc e.inv (U.map (𝟙 (op Q))) e.hom).trans he')
  have heP : _root_.SerrePositivity.CosimplicialNormalization.cofaceProjectorNat A X =
      (e.inv ≫ U.map (DoldKan.PInfty (X := _root_.SerrePositivity.CosimplicialNormalization.dualSimplicial A X)).op) ≫ e.hom :=
    (Category.assoc _ _ _).symm
  exact (Homotopy.ofEq heP).trans (H.trans (Homotopy.ofEq heI))


end SerrePositivity.CosimplicialNormalization
