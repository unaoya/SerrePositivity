module
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
概要：filtered な複体図式の対象ごとの擬同型を strict 余極限へ運ぶ。
方針：複体の図式を関手圏の複体として読み、加群の AB5 による完全な colim を使う。
規約：複体は非有界でよく、κ-compact 性や native 余極限を仮定しない。
使われ方：strict bar 比較の filtered 余極限による擬同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits HomologicalComplex
variable (R : Type u) [CommRing R] {J : Type u} [SmallCategory J]

def dgStrictComplexDiagram (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (J ⥤ ModuleCat.{u} R) ℤ where
  X n := F ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) n
  d n m :=
    { app j := (F.obj j).d n m
      naturality j k f := (F.map f).comm n m }
  shape n m h := by
    apply NatTrans.ext
    funext j
    exact (F.obj j).shape n m h
  d_comp_d' n m k _ _ := by
    apply NatTrans.ext
    funext j
    exact (F.obj j).d_comp_d n m k

def dgStrictComplexDiagramMap
    {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} (τ : F ⟶ G) :
    dgStrictComplexDiagram R F ⟶ dgStrictComplexDiagram R G where
  f n :=
    { app j := (τ.app j).f n
      naturality j k f := congrArg (fun f => f.f n) (τ.naturality f) }
  comm' n m _ := by
    apply NatTrans.ext
    funext j
    exact (τ.app j).comm n m

lemma dgStrictComplexDiagramMap_quasiIso
    {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} (τ : F ⟶ G)
    (hτ : ∀ j, QuasiIso (τ.app j)) : QuasiIso (dgStrictComplexDiagramMap R τ) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  intro j
  have he : (((evaluation J (ModuleCat.{u} R)).obj j).mapHomologicalComplex (.up ℤ)).map
      (dgStrictComplexDiagramMap R τ) = τ.app j := by ext n; rfl
  rw [he]
  exact hτ j

variable [IsFiltered J]

lemma dgStrictComplexDiagramMap_colimit_quasiIso
    {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} (τ : F ⟶ G)
    (hτ : ∀ j, QuasiIso (τ.app j)) :
    QuasiIso (((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).map
      (dgStrictComplexDiagramMap R τ)) := by
  letI := dgStrictComplexDiagramMap_quasiIso R τ hτ
  infer_instance

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
