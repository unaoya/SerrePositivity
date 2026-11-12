module
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：加法関手と実 Dold–Kan Γ の交換を、指定余積比較で構成する。
方針：Γ の各項の有限余積を保ち、単体作用素を各全射添字の成分で照合する。
規約：微分・恒等射・零射の三つの成分を保つ。対象ごとの評価に適用する。
使われ方：HA 1.2.4、G10 の図式圏の Γ と対象ごとの Hom 空間の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory Limits AlgebraicTopology SimplicialObject
open AlgebraicTopology.DoldKan
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/-- Γ の単射に対応する微分・恒等射・零射は加法関手と可換。 -/
theorem gammaMap_mapMono (K : ChainComplex C ℕ) {a b : SimplexCategory}
    (i : a ⟶ b) [Mono i] :
    Γ₀.Obj.Termwise.mapMono ((F.mapHomologicalComplex (.down ℕ)).obj K) i =
      F.map (Γ₀.Obj.Termwise.mapMono K i) := by
  unfold Γ₀.Obj.Termwise.mapMono
  split_ifs with h h'
  · subst b
    simp
  · rfl
  · simp

/-- Γ の各次数における指定余積比較。 -/
def gammaMapDegreeIso (K : ChainComplex C ℕ) (a : SimplexCategoryᵒᵖ) :
    ((Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).obj
      ((F.mapHomologicalComplex (.down ℕ)).obj K)).obj a ≅
    F.obj (((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).obj K).obj a) :=
  (PreservesCoproduct.iso F (Γ₀.Obj.summand K a)).symm

/-- 余積比較は元の全単体作用素と可換。 -/
theorem gammaMapDegreeIso_naturality (K : ChainComplex C ℕ)
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).obj
      ((F.mapHomologicalComplex (.down ℕ)).obj K)).map f ≫ (gammaMapDegreeIso F K b).hom =
    (gammaMapDegreeIso F K a).hom ≫
      F.map (((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).obj K).map f) := by
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (Γ₀.Obj.summand ((F.mapHomologicalComplex (.down ℕ)).obj K) a) s ≫
      Γ₀.Obj.map _ f ≫ sigmaComparison F (Γ₀.Obj.summand K b) =
    Sigma.ι _ s ≫ sigmaComparison F (Γ₀.Obj.summand K a) ≫ F.map (Γ₀.Obj.map K f)
  erw [Γ₀.Obj.map_on_summand₀'_assoc, ι_comp_sigmaComparison,
    ι_comp_sigmaComparison_assoc, ← F.map_comp, Γ₀.Obj.map_on_summand₀', F.map_comp,
    gammaMap_mapMono]
  rfl

/-- 加法関手で移してから Γ を取ることと、Γ の各項を移すことの指定同型。 -/
def gammaMapIso (K : ChainComplex C ℕ) :
    (Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).obj
        ((F.mapHomologicalComplex (.down ℕ)).obj K) ≅
      (Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).obj K ⋙ F :=
  NatIso.ofComponents (gammaMapDegreeIso F K) (fun f => gammaMapDegreeIso_naturality F K f)

end SerrePositivity.HomologicalAlgebra
