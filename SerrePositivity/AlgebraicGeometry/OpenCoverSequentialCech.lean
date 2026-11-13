module

public import SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinement
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSequentialComplex
public import SerrePositivity.AlgebraicGeometry.ProjectiveSequentialComplexQuasiIso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：有限被覆の細分比較を、係数前層の自然数順極限へ渡す。
方針：同じ細分写像の各段の自然性と、複体の余極限の標準同型を使う。
規約：加群の宇宙を制限せず、実際の細分写像を別の射に置き換えない。
使われ方：Frobenius 後の共通アフィン細分の同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- 交叉への制限と既存の全タプル複体を合成した、整数係数の Čech 関手。 -/
def openCoverIntCechFunctor (U : ι → Opens X) :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{v} ℤ) ⥤ CochainComplex (ModuleCat.{v} ℤ) ℕ :=
  (whiskeringLeft _ _ _).obj (openCoverCechIndexFunctor U) ⋙ fullCechComplexFunctor

/-- 細分の写像は整数係数の前層を動かす自然変換。 -/
def openCoverIntCechRefinementNatTrans (U : ι → Opens X) (V : κ → Opens X)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) :
    openCoverIntCechFunctor.{u,v} U ⟶ openCoverIntCechFunctor V where
  app P := openCoverCechRefinementMap P U V ρ hρ
  naturality {P Q} η := (openCoverCechRefinementMap_naturality U V ρ hρ η).symm

/-- 有限被覆の整数係数 Čech 関手は自然数順極限を保つ。 -/
instance openCoverIntCechFunctorPreservesSequentialColimits
    [Fintype ι] (U : ι → Opens X) :
    PreservesColimitsOfShape ℕ (openCoverIntCechFunctor.{u,v} U) := by
  dsimp only [openCoverIntCechFunctor]
  infer_instance

variable [Fintype ι] [Fintype κ]
variable (P : ℕ ⥤ (Opens X)ᵒᵖ ⥤ ModuleCat.{v} ℤ)
variable (U : ι → Opens X) (V : κ → Opens X)
variable (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))

/-- 複体の順極限比較は、同じ実際の細分写像と可換。 -/
theorem openCoverSequentialCech_refinement_naturality :
    openCoverCechRefinementMap (colimit P) U V ρ hρ ≫
        (preservesColimitIso (openCoverIntCechFunctor V) P).hom =
      (preservesColimitIso (openCoverIntCechFunctor U) P).hom ≫
        colim.map (whiskerLeft P (openCoverIntCechRefinementNatTrans U V ρ hρ)) := by
  let CU := openCoverIntCechFunctor.{u,v} U
  let CV := openCoverIntCechFunctor.{u,v} V
  let α := openCoverIntCechRefinementNatTrans.{u,v} U V ρ hρ
  change α.app (colimit P) ≫ (preservesColimitIso CV P).hom =
    (preservesColimitIso CU P).hom ≫ colim.map (whiskerLeft P α)
  apply (cancel_epi (preservesColimitIso CU P).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply colimit.hom_ext
  intro n
  rw [ι_preservesColimitIso_inv_assoc]
  rw [← Category.assoc, α.naturality (colimit.ι P n), Category.assoc,
    ι_preservesColimitIso_hom, colimit.ι_map]
  rfl

/-- 細分が各有限段の Čech H で同型なら、係数前層の順極限でも同型。
Stacks 30.2.6 の被覆比較と BST13 Lemma 3.9 の極限に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem openCoverSequentialCech_refinement_quasiIsoAt (q : ℕ)
    (h : ∀ n, QuasiIsoAt (openCoverCechRefinementMap (P.obj n) U V ρ hρ) q) :
    QuasiIsoAt (openCoverCechRefinementMap (colimit P) U V ρ hρ) q := by
  let η := whiskerLeft P (openCoverIntCechRefinementNatTrans U V ρ hρ)
  haveI : QuasiIsoAt (colim.map η) q :=
    projectiveSequentialComplexMap_quasiIsoAt η q h
  haveI : QuasiIsoAt (openCoverCechRefinementMap (colimit P) U V ρ hρ ≫
      (preservesColimitIso (openCoverIntCechFunctor V) P).hom) q := by
    rw [openCoverSequentialCech_refinement_naturality]
    infer_instance
  exact quasiIsoAt_of_comp_right
    (openCoverCechRefinementMap (colimit P) U V ρ hρ)
    (preservesColimitIso (openCoverIntCechFunctor V) P).hom q

end SerrePositivity.AlgebraicGeometry
