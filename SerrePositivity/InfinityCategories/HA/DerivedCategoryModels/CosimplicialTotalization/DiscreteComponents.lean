module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SingleComponent
public import Mathlib.Algebra.Homology.Single

/-!
概要：離散加群入力の積全複体の各次数を、元の余単体加群の次数と照合する。
方針：内部次数零の複体へ関手的に埋め込み、対角線に残る一つの成分を指定射影で取り出す。
規約：負の全次数は零。ここでは複体の同型や native 極限性はまだ主張しない。
使われ方：HA 1.2.4、G10 の加群版の交代余面複体との比較の成分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SerrePositivity.DifferentialGraded
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

/-- 各余単体加群を内部次数零の複体へ送る全関手。 -/
def discreteDiagramFunctor : CosimplicialObject (ModuleCat.{u} A) ⥤ CosimplicialObject (Complex A) :=
  (CosimplicialObject.whiskering _ _).obj (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0)

/-- 離散加群入力に制限した、同じ積全複体の全関手。 -/
def discreteTotalFunctor : CosimplicialObject (ModuleCat.{u} A) ⥤ Complex A :=
  discreteDiagramFunctor A ⋙ productTotalFunctor A

/-- 全次数 q と余単体次数 n が異なる成分は零。 -/
theorem discreteComponent_isZero (X : CosimplicialObject (ModuleCat.{u} A)) (q : ℤ) (n : ℕ)
    (h : q ≠ n) :
    IsZero ((((discreteDiagramFunctor A).obj X).obj ⦋n⦌).X (q-n)) :=
  HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (X.obj ⦋n⦌) (q-n) (by omega)

/-- 離散加群入力の負の全次数は零。 -/
theorem discreteTotal_negative_isZero (X : CosimplicialObject (ModuleCat.{u} A)) (q : ℤ)
    (hq : q<0) : IsZero (((discreteTotalFunctor A).obj X).X q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply component_hom_ext ((discreteDiagramFunctor A).obj X) q
  intro n
  exact (discreteComponent_isZero A X q n (by omega)).eq_of_tgt _ _

/-- 全次数 n の元の離散加群成分を取り出す指定同型。 -/
def discreteSelfComponentIso (X : CosimplicialObject (ModuleCat.{u} A)) (n : ℕ) :
    (((discreteDiagramFunctor A).obj X).obj ⦋n⦌).X ((n : ℤ)-n) ≅ X.obj ⦋n⦌ :=
  HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (X.obj ⦋n⦌) ((n : ℤ)-n) (by omega)

/-- 非負全次数 n の積全複体は、元の余単体次数 n の加群と同型。 -/
def discreteTotalDegreeIso (X : CosimplicialObject (ModuleCat.{u} A)) (n : ℕ) :
    ((discreteTotalFunctor A).obj X).X (n : ℤ) ≅ X.obj ⦋n⦌ :=
  singleComponentIso ((discreteDiagramFunctor A).obj X) n n
    (fun m hm => discreteComponent_isZero A X n m (by omega)) ≪≫
      discreteSelfComponentIso A X n

/-- 離散複体の指定成分同型は元の加群図式の射と可換。 -/
theorem discreteSelfComponentIso_naturality
    {X Y : CosimplicialObject (ModuleCat.{u} A)} (f : X ⟶ Y) (n : ℕ) :
    (((discreteDiagramFunctor A).map f).app ⦋n⦌).f ((n : ℤ)-n) ≫
      (discreteSelfComponentIso A Y n).hom =
        (discreteSelfComponentIso A X n).hom ≫ f.app ⦋n⦌ := by
  have h (q : ℤ) (hq : q=0) :
      ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map (f.app ⦋n⦌)).f q ≫
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (Y.obj ⦋n⦌) q hq).hom =
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (X.obj ⦋n⦌) q hq).hom ≫ f.app ⦋n⦌ := by
    subst q
    simpa [HomologicalComplex.singleObjXSelf] using
      (HomologicalComplex.singleCompEvalIsoSelf (ModuleCat.{u} A) (.up ℤ) 0).hom.naturality (f.app ⦋n⦌)
  exact h _ (by omega)

/-- 非負次数の同型は、同じ積 total 関手の射と厳密に可換。 -/
theorem discreteTotalDegreeIso_naturality
    {X Y : CosimplicialObject (ModuleCat.{u} A)} (f : X ⟶ Y) (n : ℕ) :
    ((discreteTotalFunctor A).map f).f (n : ℤ) ≫ (discreteTotalDegreeIso A Y n).hom =
      (discreteTotalDegreeIso A X n).hom ≫ f.app ⦋n⦌ := by
  dsimp only [discreteTotalDegreeIso, singleComponentIso, Iso.trans_hom,
    discreteTotalFunctor, Functor.comp_map]
  rw [← Category.assoc, componentπ_naturality, Category.assoc,
    discreteSelfComponentIso_naturality, ← Category.assoc]

/-- 非負次数の照合を、加群図式の圏上の自然同型として返す。 -/
def discreteTotalDegreeNatIso (n : ℕ) :
    discreteTotalFunctor A ⋙ HomologicalComplex.eval _ _ (n : ℤ) ≅
      (evaluation SimplexCategory (ModuleCat.{u} A)).obj ⦋n⦌ :=
  NatIso.ofComponents (fun X => discreteTotalDegreeIso A X n)
    (fun f => discreteTotalDegreeIso_naturality A f n)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
