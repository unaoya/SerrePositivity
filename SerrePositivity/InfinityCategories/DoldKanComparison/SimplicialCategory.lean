module

public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardVertices
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory

/-!
# Dold–Kan の単体的圏と coherent nerve

概要：閉零射の圏を DK Hom と AW 合成で単体的圏にし、その coherent nerve を定義する。
方針：零単体と閉零射の同値を使って豊穣と通常の圏を整合させ、局所 Kan 性から γ1 を使う。
規約：標準成分の Hom は Mathlib Γ と自然同型で同定されている。
使われ方：HA 1.3.1.13–1.3.1.17、Kerodon 2.5.9 の dg nerve との比較の始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：閉零射の圏に DK Hom と AW 合成の単体的圏構造を入れる。
方針：閉零射と標準零単体の同値を単位からの射へ移し、恒等射と合成の保存を使う。
規約：Hom は係数環と同じ宇宙 u の単体集合。
使われ方：HA 1.3.1.13 の C_Δ。 -/
instance doldKanSimplicialCategory : SimplicialCategory (ClosedCategory R D) where
  toEnrichedCategory := standardEnrichedCategory (R := R) (D := D)
  homEquiv {x y} := (closedStandardVertexEquiv (R := R) (D := D) x y).trans
    (standardHomSpace (R := R) (D := D) x y).unitHomEquiv.symm
  homEquiv_id x := by
    apply (standardHomSpace (R := R) (D := D) x x).unitHomEquiv.injective
    change (standardHomSpace (R := R) (D := D) x x).unitHomEquiv
      ((standardHomSpace (R := R) (D := D) x x).unitHomEquiv.symm
        (closedStandardVertexEquiv (R := R) (D := D) x x (𝟙 x))) =
          standardUnit (R := R) (D := D) x 0
    rw [Equiv.apply_symm_apply]
    exact closedStandardVertexEquiv_id x
  homEquiv_comp {x y z} f g := by
    apply (standardHomSpace (R := R) (D := D) x z).unitHomEquiv.injective
    change (standardHomSpace (R := R) (D := D) x z).unitHomEquiv
      ((standardHomSpace (R := R) (D := D) x z).unitHomEquiv.symm
        (closedStandardVertexEquiv (R := R) (D := D) x z (f ≫ g))) =
      standardAW
        ((standardHomSpace (R := R) (D := D) y z).unitHomEquiv
          ((standardHomSpace (R := R) (D := D) y z).unitHomEquiv.symm
            (closedStandardVertexEquiv (R := R) (D := D) y z g)))
        ((standardHomSpace (R := R) (D := D) x y).unitHomEquiv
          ((standardHomSpace (R := R) (D := D) x y).unitHomEquiv.symm
            (closedStandardVertexEquiv (R := R) (D := D) x y f)))
    simp only [Equiv.apply_symm_apply]
    exact closedStandardVertexEquiv_comp f g

/-- 概要：DK の単体的圏の全ての豊穣 Hom は Kan 複体である。
方針：標準成分模型の直接の線形充填から得た Kan 性を使う。
規約：追加の充填仮定はない。
使われ方：HA 1.3.1.14 の局所 Kan 性。 -/
instance doldKanSimplicialCategory_locallyKan (x y : ClosedCategory R D) :
    SSet.KanComplex (SimplicialCategory.sHom x y) :=
  standardHomSpaceKan (R := R) (D := D) x y

/-- 概要：DK の単体的圏の豊穣 Hom は実際の Mathlib Γ の Hom と自然同型である。
方針：標準成分模型と Γ の単体的加群の同型を忘却する。
規約：全ての面と退化に関する自然同型。
使われ方：HA 1.3.1.13 の Hom = DK(τ≤0 Hom) の同定。 -/
def doldKanSimplicialHomIso (x y : ClosedCategory R D) :
    SimplicialCategory.sHom x y ≅ doldKanHomSpace (R := R) (D := D) x y :=
  Functor.isoWhiskerRight (standardDoldKanModuleIso (R := R) (D := D) x y)
    (forget (ModuleCat.{u} R))

/-- 概要：Dold–Kan で豊穣化した dg 圏の coherent nerve を定義する。
方針：閉零射の圏上の単体的圏構造に Mathlib の SimplicialNerve を適用する。
規約：対象と係数環の宇宙を合わせた SSet の宇宙を使う。
使われ方：HA 1.3.1.16–1.3.1.17 の dg nerve への比較の始域。 -/
def doldKanCoherentNerve : SSet.{max u v} := SimplicialNerve (ClosedCategory R D)

/-- 概要：DK で豊穣化した dg 圏の coherent nerve は quasicategory である。
方針：局所 Kan 性と γ1 の一般定理を適用する。
規約：dg 圏以外の充填や整合性の仮定はない。
使われ方：HA 1.3.1.17 の比較対象となる ∞ 圏。 -/
instance doldKanCoherentNerve_quasicategory :
    SSet.Quasicategory (doldKanCoherentNerve (R := R) (D := D)) :=
  Coherent.simplicialNerve_quasicategory (ClosedCategory R D)

end SerrePositivity.InfinityCategories.DoldKanComparison
