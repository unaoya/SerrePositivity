module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # 右 dg 加群の Hom end

全豊穣 Hom に対する自然性を二つの chain map の equalizer として課す。
閉次数零の射だけに対する通常の自然性では代用しない。
対象族 D が Hom 加群の宇宙 u に small であることを明示する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

local instance : HasProductsOfShape D (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape
local instance : HasProductsOfShape (D × D) (ModuleCat.{u} A) := ModuleCat.hasLimitsOfShape

/-- 全対象上の Hom 複体の直積。 -/
abbrev homFamily (M N : RightModule A D) : D → Complex A :=
  fun x => homComplex A (M.obj (op x)) (N.obj (op x))

/-- 自然変換候補の全対象での直積。 -/
abbrev homCandidates (M N : RightModule A D) : Complex A := ∏ᶜ homFamily A D M N

/-- 全豊穣 Hom に関する自然性の値域。二重 Hom で全次数を保持する。 -/
abbrev homRelations (M N : RightModule A D) : D × D → Complex A :=
  fun xy => homComplex A (op xy.1 ⟶[Complex A] op xy.2)
    (homComplex A (M.obj (op xy.1)) (N.obj (op xy.2)))

/-- 自然性の左辺の転置前の chain map。 -/
def homNaturalityLeft (M N : RightModule A D) (x y : D) :
    homCandidates A D M N ⊗ (op x ⟶[Complex A] op y) ⟶
      homComplex A (M.obj (op x)) (N.obj (op y)) :=
  (β_ _ _).hom ≫ (M.map (op x) (op y) ⊗ₘ Pi.π (homFamily A D M N) y) ≫
    enrichedComposition (M.obj (op x)) (M.obj (op y)) (N.obj (op y))

/-- 自然性の右辺の転置前の chain map。 -/
def homNaturalityRight (M N : RightModule A D) (x y : D) :
    homCandidates A D M N ⊗ (op x ⟶[Complex A] op y) ⟶
      homComplex A (M.obj (op x)) (N.obj (op y)) :=
  (Pi.π (homFamily A D M N) x ⊗ₘ N.map (op x) (op y)) ≫
    enrichedComposition (M.obj (op x)) (N.obj (op x)) (N.obj (op y))

/-- 全対の自然性の左辺を同時に保持する射。 -/
def homRelationsLeft (M N : RightModule A D) :
    homCandidates A D M N ⟶ ∏ᶜ homRelations A D M N :=
  Pi.lift (fun xy => curryRight (homNaturalityLeft A D M N xy.1 xy.2))

/-- 全対の自然性の右辺を同時に保持する射。 -/
def homRelationsRight (M N : RightModule A D) :
    homCandidates A D M N ⟶ ∏ᶜ homRelations A D M N :=
  Pi.lift (fun xy => curryRight (homNaturalityRight A D M N xy.1 xy.2))

/-- 右 dg 加群の Hom 複体。全次数の豊穣自然性を課す end。 -/
abbrev moduleHom (M N : RightModule A D) : Complex A :=
  equalizer (homRelationsLeft A D M N) (homRelationsRight A D M N)

/-- Hom end の対象 x における評価 chain map。 -/
abbrev moduleHomπ (M N : RightModule A D) (x : D) :
    moduleHom A D M N ⟶ homComplex A (M.obj (op x)) (N.obj (op x)) :=
  equalizer.ι _ _ ≫ Pi.π (homFamily A D M N) x

/-- Hom end への射は全対象の成分で判定できる。 -/
lemma moduleHom_ext {M N : RightModule A D} {K : Complex A}
    {f g : K ⟶ moduleHom A D M N}
    (h : ∀ x, f ≫ moduleHomπ A D M N x = g ≫ moduleHomπ A D M N x) : f = g := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro x
  exact h x
/-- Hom 候補への射を自然性の左辺へ前合成する公式。 -/
lemma homNaturalityLeft_precomp (M N : RightModule A D) {K : Complex A}
    (k : K ⟶ homCandidates A D M N) (x y : D) :
    (k ⊗ₘ 𝟙 (op x ⟶[Complex A] op y)) ≫ homNaturalityLeft A D M N x y =
      (β_ K (op x ⟶[Complex A] op y)).hom ≫
        (M.map (op x) (op y) ⊗ₘ (k ≫ Pi.π (homFamily A D M N) y)) ≫
          enrichedComposition (M.obj (op x)) (M.obj (op y)) (N.obj (op y)) := by
  dsimp only [homNaturalityLeft]
  rw [← Category.assoc, ← Category.assoc, BraidedCategory.braiding_naturality,
    Category.assoc, Category.assoc, tensorHom_comp_tensorHom_assoc]
  simp

/-- Hom 候補への射を自然性の右辺へ前合成する公式。 -/
lemma homNaturalityRight_precomp (M N : RightModule A D) {K : Complex A}
    (k : K ⟶ homCandidates A D M N) (x y : D) :
    (k ⊗ₘ 𝟙 (op x ⟶[Complex A] op y)) ≫ homNaturalityRight A D M N x y =
      ((k ≫ Pi.π (homFamily A D M N) x) ⊗ₘ N.map (op x) (op y)) ≫
        enrichedComposition (M.obj (op x)) (N.obj (op x)) (N.obj (op y)) := by
  dsimp only [homNaturalityRight]
  rw [tensorHom_comp_tensorHom_assoc]
  simp

/-- Hom end に入るための条件は全次数の豊穣自然性と同値。 -/
lemma homRelations_eq_iff (M N : RightModule A D) {K : Complex A}
    (k : K ⟶ homCandidates A D M N) :
    k ≫ homRelationsLeft A D M N = k ≫ homRelationsRight A D M N ↔
      ∀ x y : D,
        (β_ K (op x ⟶[Complex A] op y)).hom ≫
          (M.map (op x) (op y) ⊗ₘ (k ≫ Pi.π (homFamily A D M N) y)) ≫
            enrichedComposition (M.obj (op x)) (M.obj (op y)) (N.obj (op y)) =
        ((k ≫ Pi.π (homFamily A D M N) x) ⊗ₘ N.map (op x) (op y)) ≫
          enrichedComposition (M.obj (op x)) (N.obj (op x)) (N.obj (op y)) := by
  constructor
  · intro h x y
    have hp := congrArg (fun f => f ≫ Pi.π (homRelations A D M N) (x, y)) h
    simp only [homRelationsLeft, homRelationsRight, Category.assoc, homRelations,
      Pi.lift_comp_π] at hp
    have ht := congrArg uncurryRight hp
    rw [← curryRight_naturality_source, ← curryRight_naturality_source,
      uncurryRight_curryRight, uncurryRight_curryRight,
      homNaturalityLeft_precomp, homNaturalityRight_precomp] at ht
    exact ht
  · intro h
    apply Pi.hom_ext
    rintro ⟨x, y⟩
    simp only [homRelationsLeft, homRelationsRight, Category.assoc, homRelations,
      Pi.lift_comp_π]
    rw [← curryRight_naturality_source, ← curryRight_naturality_source,
      homNaturalityLeft_precomp, homNaturalityRight_precomp, h x y]

/-- パラメータ K を持つ全次数の豊穣自然変換。Mathlib の GradedNatTrans を再利用する。 -/
abbrev ModuleParamTrans (K : Complex A) (M N : RightModule A D) :=
  GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctor

/-- Hom end の普遍性：射 K→Hom(M,N) は K パラメータ付き豊穣自然変換。 -/
def moduleHomEquiv (K : Complex A) (M N : RightModule A D) :
    (K ⟶ moduleHom A D M N) ≃ ModuleParamTrans A D K M N where
  toFun f :=
    { app x := f ≫ moduleHomπ A D M N x.unop
      naturality x y := by
        have hh := congrArg (fun l => f ≫ l) (equalizer.condition
          (homRelationsLeft A D M N) (homRelationsRight A D M N))
        rw [← Category.assoc, ← Category.assoc] at hh
        have hp := (homRelations_eq_iff A D M N _).1 hh x.unop y.unop
        exact hp }
  invFun τ := equalizer.lift (Pi.lift (fun x => τ.app (op x))) (by
    apply (homRelations_eq_iff A D M N _).2
    intro x y
    simp only [homFamily, Pi.lift_comp_π]
    exact τ.naturality (op x) (op y))
  left_inv f := by
    apply moduleHom_ext
    intro x
    simp only [moduleHomπ, equalizer.lift_ι_assoc, Pi.lift_comp_π]
  right_inv τ := by
    apply GradedNatTrans.ext
    funext x
    simp only [moduleHomπ, equalizer.lift_ι_assoc, Pi.lift_comp_π]
end SerrePositivity.DifferentialGraded
