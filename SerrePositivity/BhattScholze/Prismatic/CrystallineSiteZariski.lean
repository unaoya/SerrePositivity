module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineSitePullback
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Sieves.Presieve

/-!
# affine 結晶厚化の Zariski 被覆族と生成位相

## 概要
有限個の主開局所化が単位イデアルを生成する被覆族を定める。

## 方針
対象の環上の局所化条件を使い、被覆族が生成する最小の Grothendieck 位相を取る。

## 規約
環の向きの局所化を反転してサイトの被覆とする。小さい模型への移送は別に行う。

## 使われ方
Berthelot III.4、Stacks 07HM–07HN。構造環の層性と引き戻しの入力。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}

namespace CrysOver
/-- 主開局所化による有限 Zariski 被覆族。分冪イデアルも局所化する。 -/
def IsZariskiFamily {ι : Type u} [Finite ι] {X : CrysOver p γ R κ}
    (Y : ι → CrysOver p γ R κ) (f : ∀ i, X ⟶ Y i) : Prop :=
  ∃ g : ι → X.B, Ideal.span (Set.range g) = ⊤ ∧ ∀ i,
    letI := (f i).toAlgHom.toRingHom.toAlgebra
    IsLocalization.Away (g i) (Y i).B ∧
      (Y i).JB = X.JB.map (f i).toAlgHom.toRingHom

/-- 剰余代数の引き戻しは主開 Zariski 被覆族を保つ。 -/
theorem IsZariskiFamily.pullback {R' : Type u} [CommRing R'] [Algebra (k ⧸ J) R']
    (a : R →ₐ[k ⧸ J] R') {ι : Type u} [Finite ι] {X : CrysOver p γ R' κ}
    {Y : ι → CrysOver p γ R' κ} {f : ∀ i, X ⟶ Y i} (h : IsZariskiFamily Y f) :
    IsZariskiFamily (fun i => (crysPullback p γ κ a).obj (Y i))
      (fun i => (crysPullback p γ κ a).map (f i)) := h
end CrysOver

/-- 有限主開被覆族の反転で生成する、大きい affine 結晶サイトの位相。 -/
def crystallineLargeZariskiTopology :
    GrothendieckTopology (CrysOver p γ R κ)ᵒᵖ :=
  sInf { T | ∀ {ι : Type u} [Finite ι] {X : CrysOver p γ R κ}
    (Y : ι → CrysOver p γ R κ) (f : ∀ i, X ⟶ Y i),
    CrysOver.IsZariskiFamily Y f →
      Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op))
        ∈ T (Opposite.op X) }

/-- 指定された有限主開被覆は生成位相で被覆となる。 -/
theorem crystallineLargeZariskiTopology_cover {ι : Type u} [Finite ι]
    {X : CrysOver p γ R κ} (Y : ι → CrysOver p γ R κ) (f : ∀ i, X ⟶ Y i)
    (h : CrysOver.IsZariskiFamily Y f) :
    Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op))
      ∈ crystallineLargeZariskiTopology (Opposite.op X) := by
  exact (GrothendieckTopology.mem_sInf _ _).mpr fun T hT => hT Y f h

/-- すべての主開被覆を含む位相は結晶 Zariski 位相を含む。 -/
theorem crystallineLargeZariskiTopology_le (T : GrothendieckTopology (CrysOver p γ R κ)ᵒᵖ)
    (hT : ∀ {ι : Type u} [Finite ι] {X : CrysOver p γ R κ}
      (Y : ι → CrysOver p γ R κ) (f : ∀ i, X ⟶ Y i),
      CrysOver.IsZariskiFamily Y f →
        Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op))
          ∈ T (Opposite.op X)) : crystallineLargeZariskiTopology ≤ T :=
  sInf_le hT

end SerrePositivity.BhattScholze.Prismatic
