module
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! # 厳密 dg 関手間の全次数自然変換の Hom end
概要：任意の標的 dg 圏への厳密 dg 関手の全次数 Hom 複体を構成する。
方針：全対象の Hom の積に、全 Hom 複体に関する自然性を等化子で課す。
規約：閉零射だけに対する通常の自然性では代用しない。使われ方：K の dg 入力豊穣。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]
local instance : HasProductsOfShape D (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape
local instance : HasProductsOfShape (D × D) (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape

/-- 全対象上の Hom 複体の直積。 -/
abbrev dgFunctorHomFamily (M N : DGFunctor A D E) : D → Complex A :=
  fun x => homObject A E (M.obj x) (N.obj x)

/-- 自然変換候補の全対象での直積。 -/
abbrev dgFunctorHomCandidates (M N : DGFunctor A D E) : Complex A := ∏ᶜ dgFunctorHomFamily A D E M N

/-- 全豊穣 Hom に関する自然性の値域。二重 Hom で全次数を保持する。 -/
abbrev dgFunctorHomRelations (M N : DGFunctor A D E) : D × D → Complex A :=
  fun xy => homComplex A (xy.1 ⟶[Complex A] xy.2)
    (homObject A E (M.obj xy.1) (N.obj xy.2))

/-- 自然性の左辺の転置前の chain map。 -/
def dgFunctorHomNaturalityLeft (M N : DGFunctor A D E) (x y : D) :
    dgFunctorHomCandidates A D E M N ⊗ (x ⟶[Complex A] y) ⟶
      homObject A E (M.obj x) (N.obj y) :=
  (β_ _ _).hom ≫ (M.map x y ⊗ₘ Pi.π (dgFunctorHomFamily A D E M N) y) ≫
    eComp (Complex A) (M.obj x) (M.obj y) (N.obj y)

/-- 自然性の右辺の転置前の chain map。 -/
def dgFunctorHomNaturalityRight (M N : DGFunctor A D E) (x y : D) :
    dgFunctorHomCandidates A D E M N ⊗ (x ⟶[Complex A] y) ⟶
      homObject A E (M.obj x) (N.obj y) :=
  (Pi.π (dgFunctorHomFamily A D E M N) x ⊗ₘ N.map x y) ≫
    eComp (Complex A) (M.obj x) (N.obj x) (N.obj y)

/-- 全対の自然性の左辺を同時に保持する射。 -/
def dgFunctorHomRelationsLeft (M N : DGFunctor A D E) :
    dgFunctorHomCandidates A D E M N ⟶ ∏ᶜ dgFunctorHomRelations A D E M N :=
  Pi.lift (fun xy => curryRight (dgFunctorHomNaturalityLeft A D E M N xy.1 xy.2))

/-- 全対の自然性の右辺を同時に保持する射。 -/
def dgFunctorHomRelationsRight (M N : DGFunctor A D E) :
    dgFunctorHomCandidates A D E M N ⟶ ∏ᶜ dgFunctorHomRelations A D E M N :=
  Pi.lift (fun xy => curryRight (dgFunctorHomNaturalityRight A D E M N xy.1 xy.2))

/-- dg 関手の Hom 複体。全次数の豊穣自然性を課す end。 -/
abbrev dgFunctorHom (M N : DGFunctor A D E) : Complex A :=
  equalizer (dgFunctorHomRelationsLeft A D E M N) (dgFunctorHomRelationsRight A D E M N)

/-- Hom end の対象 x における評価 chain map。 -/
abbrev dgFunctorHomπ (M N : DGFunctor A D E) (x : D) :
    dgFunctorHom A D E M N ⟶ homObject A E (M.obj x) (N.obj x) :=
  equalizer.ι _ _ ≫ Pi.π (dgFunctorHomFamily A D E M N) x

/-- Hom end への射は全対象の成分で判定できる。 -/
lemma dgFunctorHom_ext {M N : DGFunctor A D E} {K : Complex A}
    {f g : K ⟶ dgFunctorHom A D E M N}
    (h : ∀ x, f ≫ dgFunctorHomπ A D E M N x = g ≫ dgFunctorHomπ A D E M N x) : f = g := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro x
  exact h x
/-- Hom 候補への射を自然性の左辺へ前合成する公式。 -/
lemma dgFunctorHomNaturalityLeft_precomp (M N : DGFunctor A D E) {K : Complex A}
    (k : K ⟶ dgFunctorHomCandidates A D E M N) (x y : D) :
    (k ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ dgFunctorHomNaturalityLeft A D E M N x y =
      (β_ K (x ⟶[Complex A] y)).hom ≫
        (M.map x y ⊗ₘ (k ≫ Pi.π (dgFunctorHomFamily A D E M N) y)) ≫
          eComp (Complex A) (M.obj x) (M.obj y) (N.obj y) := by
  dsimp only [dgFunctorHomNaturalityLeft]
  rw [← Category.assoc, ← Category.assoc, BraidedCategory.braiding_naturality,
    Category.assoc, Category.assoc, tensorHom_comp_tensorHom_assoc]
  simp

/-- Hom 候補への射を自然性の右辺へ前合成する公式。 -/
lemma dgFunctorHomNaturalityRight_precomp (M N : DGFunctor A D E) {K : Complex A}
    (k : K ⟶ dgFunctorHomCandidates A D E M N) (x y : D) :
    (k ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ dgFunctorHomNaturalityRight A D E M N x y =
      ((k ≫ Pi.π (dgFunctorHomFamily A D E M N) x) ⊗ₘ N.map x y) ≫
        eComp (Complex A) (M.obj x) (N.obj x) (N.obj y) := by
  dsimp only [dgFunctorHomNaturalityRight]
  rw [tensorHom_comp_tensorHom_assoc]
  simp

end SerrePositivity.KST.SConstruction
