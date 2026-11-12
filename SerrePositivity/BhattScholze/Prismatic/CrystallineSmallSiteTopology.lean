module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineSiteSmall
public import SerrePositivity.BhattScholze.Prismatic.CrystallineSiteZariski

/-!
# 小さい affine 結晶サイトの位相と構造前層

## 概要
本質的に小さい厚化の圏を小さい模型へ移し、主開被覆が生成する位相を定める。

## 方針
小さい模型の逆関手で被覆条件を判定する。構造前層は同じ逆関手の台環。

## 規約
構造環は基底の下の可換環の値を取る通常の前層。層性は別に証明する。

## 使われ方
Berthelot III.4、Stacks 07HM–07HN。結晶サイトの古典的な入口。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R] (κ : Cardinal.{u})

/-- 小さい模型における有限主開 Zariski 被覆族。 -/
def IsCrystallineZariskiFamily {ι : Type u} [Finite ι]
    {X : CrysOverSmall p γ R κ} (Y : ι → CrysOverSmall p γ R κ)
    (f : ∀ i, X ⟶ Y i) : Prop :=
  CrysOver.IsZariskiFamily
    (fun i => (equivSmallModel (CrysOver p γ R κ)).inverse.obj (Y i))
    (fun i => (equivSmallModel (CrysOver p γ R κ)).inverse.map (f i))

/-- 小さい affine 結晶サイトの Zariski 位相。 -/
def zariskiTopology : GrothendieckTopology (CrystallineSite p γ R κ) :=
  sInf { T | ∀ {ι : Type u} [Finite ι] {X : CrysOverSmall p γ R κ}
    (Y : ι → CrysOverSmall p γ R κ) (f : ∀ i, X ⟶ Y i),
    IsCrystallineZariskiFamily p γ R κ Y f →
      Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op))
        ∈ T (Opposite.op X) }

/-- 指定された主開被覆族は小さいサイトでも被覆となる。 -/
theorem zariskiTopology_cover {ι : Type u} [Finite ι]
    {X : CrysOverSmall p γ R κ} (Y : ι → CrysOverSmall p γ R κ) (f : ∀ i, X ⟶ Y i)
    (h : IsCrystallineZariskiFamily p γ R κ Y f) :
    Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op))
      ∈ zariskiTopology p γ R κ (Opposite.op X) := by
  exact (GrothendieckTopology.mem_sInf _ _).mpr fun T hT => hT Y f h

/-- 構造環の前層。小さい模型の逆関手から厚化の台環を取る。 -/
def crystallineStructureRing :
    (CrystallineSite p γ R κ)ᵒᵖ ⥤ Under (CommRingCat.of k) :=
  unopUnop _ ⋙ (equivSmallModel (CrysOver p γ R κ)).inverse ⋙ crysAlgebras p γ R κ

variable {R' : Type u} [CommRing R'] [Algebra (k ⧸ J) R']

/-- 剰余代数の射に沿う、小さい結晶サイトの圏の関手。 -/
def crysPullbackSite (f : R →ₐ[k ⧸ J] R') :
    CrystallineSite p γ R' κ ⥤ CrystallineSite p γ R κ :=
  ((equivSmallModel (CrysOver p γ R' κ)).inverse ⋙ crysPullback p γ κ f ⋙
    (equivSmallModel (CrysOver p γ R κ)).functor).op

end SerrePositivity.BhattScholze.Prismatic
