module
public import SerrePositivity.InfinityCategories.Derived.PinchedRelativeHomotopy
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition

/-! # 指定された実相対ホモトピーの Hom 鎖写像による輸送

概要：構成済みホモトピーを後合成し、全境界上の定値性を厳密に保持する。
方針：実 pinched 鎖写像と線形単体写像の一致、結合則、全境界の定値式を使う。
規約：ホモトピーを再選択しない。使われ方：共通分母の追加細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
  DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E T : Type v}
variable [DGCategory A D] [DGCategory A E] [DGCategory A T]
variable {x y : D} {x' y' : E} {x'' y'' : T}

/-- 実単体写像の Hom 鎖写像による後合成は、線形単体の像と一致。 -/
lemma pinchedLinearSimplexMap_yoneda (φ : homObject A D x y ⟶ homObject A E x' y')
    {n : ℕ} (s : LinearSimplex A x y n) :
    SSet.yonedaEquiv.symm s.toPinched ≫ pinchedHomChainMap φ =
      SSet.yonedaEquiv.symm (pinchedLinearSimplexMap φ s).toPinched := by
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  change (pinchedLinearSimplexMap φ (toLinearSimplex s.toPinched)).toPinched = _
  rw [LinearSimplex.toLinearSimplex_toPinched]

/-- 指定した実相対ホモトピーを鎖写像で後合成する。 -/
def PinchedRelativeHomotopy.map {n : ℕ} {s t : LinearSimplex A x y n}
    (H : PinchedRelativeHomotopy s t) (φ : homObject A D x y ⟶ homObject A E x' y') :
    PinchedRelativeHomotopy (pinchedLinearSimplexMap φ s) (pinchedLinearSimplexMap φ t) where
  homotopy := {
    h := H.homotopy.h ≫ pinchedHomChainMap φ
    h₀ := by
      change SSet.ι₀ ≫ (H.homotopy.h ≫ pinchedHomChainMap φ) =
        SSet.yonedaEquiv.symm (pinchedLinearSimplexMap φ t).toPinched
      rw [← Category.assoc, H.homotopy.h₀, pinchedLinearSimplexMap_yoneda]
    h₁ := by
      change SSet.ι₁ ≫ (H.homotopy.h ≫ pinchedHomChainMap φ) =
        SSet.yonedaEquiv.symm (pinchedLinearSimplexMap φ s).toPinched
      rw [← Category.assoc, H.homotopy.h₁, pinchedLinearSimplexMap_yoneda]
    rel := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.2 }
  boundary := by
    change _ ≫ (H.homotopy.h ≫ pinchedHomChainMap φ) = _
    rw [← Category.assoc, H.boundary, Category.assoc, Category.assoc,
      pinchedLinearSimplexMap_yoneda]

/-- 輸送した実ホモトピーの台は、指定した後合成そのもの。 -/
lemma PinchedRelativeHomotopy.map_h {n : ℕ} {s t : LinearSimplex A x y n}
    (H : PinchedRelativeHomotopy s t) (φ : homObject A D x y ⟶ homObject A E x' y') :
    (H.map φ).homotopy.h = H.homotopy.h ≫ pinchedHomChainMap φ := rfl

/-- 二回の輸送は、実ホモトピーの台で合成鎖写像による輸送と厳密に一致。 -/
lemma PinchedRelativeHomotopy.map_comp_h {n : ℕ} {s t : LinearSimplex A x y n}
    (H : PinchedRelativeHomotopy s t) (φ : homObject A D x y ⟶ homObject A E x' y')
    (ψ : homObject A E x' y' ⟶ homObject A T x'' y'') :
    ((H.map φ).map ψ).homotopy.h = (H.map (φ ≫ ψ)).homotopy.h := by
  change (H.homotopy.h ≫ _) ≫ _ = H.homotopy.h ≫ _
  rw [pinchedHomChainMap_comp, Category.assoc]

/-- 恒等鎖写像による輸送は実ホモトピーの台を変えない。 -/
lemma PinchedRelativeHomotopy.map_id_h {n : ℕ} {s t : LinearSimplex A x y n}
    (H : PinchedRelativeHomotopy s t) :
    (H.map (𝟙 _)).homotopy.h = H.homotopy.h := by
  rw [H.map_h, pinchedHomChainMap_id, Category.comp_id]

/-- 両端の指定等式による相対ホモトピーの移送。 -/
def PinchedRelativeHomotopy.copy {n : ℕ} {s t s' t' : LinearSimplex A x y n}
    (H : PinchedRelativeHomotopy s t) (hs : s = s') (ht : t = t') :
    PinchedRelativeHomotopy s' t' := by
  subst hs
  subst ht
  exact H

/-- 両端の等式による移送は、実ホモトピーの台を変えない。 -/
lemma PinchedRelativeHomotopy.copy_h {n : ℕ} {s t s' t' : LinearSimplex A x y n}
    (H : PinchedRelativeHomotopy s t) (hs : s = s') (ht : t = t') :
    (H.copy hs ht).homotopy.h = H.homotopy.h := by
  subst hs
  subst ht
  rfl

end SerrePositivity.InfinityCategories
