module

public import SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopyComponents
import all SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopyComponents
import all Mathlib.Algebra.Homology.TotalComplex

/-!
# 非有界二重複体の横ホモトピーの全複体への移送

## 概要
内側の鎖写像で与えられた横方向の鎖ホモトピーを、直和全複体の鎖ホモトピーへ移す。

## 方針
各直和因子で横のホモトピー方程式を使う。縦微分の二項は横次数の符号の差で相殺する。

## 規約
両方向とも整数次数で、有界性・対角線の有限性・収束の仮定は置かない。

## 使われ方
HA 1.2.4、Weibel §1.2。実現の比較に使う同じ射と指定ホモトピーの保存。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)}
variable [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]
variable {f g : K ⟶ L} (h : Homotopy f g)

/-- 横ホモトピーの全次数成分は、同じ全複体の射に対するホモトピー方程式を満たす。 -/
theorem totalHorizontalComponent_comm (n : ℤ) :
    (HomologicalComplex₂.total.map f (.up ℤ)).f n =
      (K.total (.up ℤ)).d n (n + 1) ≫
        totalHorizontalComponent (fun a => h.hom a (a - 1)) (n + 1) n +
      totalHorizontalComponent (fun a => h.hom a (a - 1)) n (n - 1) ≫
        (L.total (.up ℤ)).d (n - 1) n +
      (HomologicalComplex₂.total.map g (.up ℤ)).f n := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  have h₀ := h.comm a
  rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel a (a + 1)),
    prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (a - 1) a)] at h₀
  have h₀b := congrArg (fun z => z.f b) h₀
  have hsign : (ComplexShape.up ℤ).ε (a - 1) = -(ComplexShape.up ℤ).ε a := by
    have hs := (ComplexShape.up ℤ).ε_succ
      (p := a - 1) (q := a) (by simp)
    calc
      _ = -(-(ComplexShape.up ℤ).ε (a - 1)) := (neg_neg _).symm
      _ = _ := congrArg Neg.neg hs.symm
  rw [K.ιTotal_map L f (.up ℤ), comp_add, comp_add,
    K.ιTotal_map L g (.up ℤ)]
  rw [← Category.assoc, ι_totalDifferential, add_comp,
    Linear.units_smul_comp, Category.assoc,
    ι_totalHorizontalComponent, Category.assoc, ι_totalHorizontalComponent]
  rw [ι_totalHorizontalComponent_assoc]
  simp only [L.ιTotalOrZero_eq (.up ℤ) (a - 1) b (n - 1) (by dsimp; omega),
    L.ιTotalOrZero_eq (.up ℤ) (a + 1 - 1) b n (by dsimp; omega),
    L.ιTotalOrZero_eq (.up ℤ) (a - 1) (b + 1) n (by dsimp; omega)]
  have hdL : L.ιTotal (.up ℤ) (a - 1) b (n - 1) (by dsimp; omega) ≫
      (L.total (.up ℤ)).d (n - 1) n =
      (L.d (a - 1) a).f b ≫ L.ιTotal (.up ℤ) a b n hab +
      (ComplexShape.up ℤ).ε (a - 1) • ((L.X (a - 1)).d b (b + 1) ≫
        L.ιTotal (.up ℤ) (a - 1) (b + 1) n (by dsimp; omega)) := by
    change _ ≫ (L.D₁ (.up ℤ) (n - 1) n + L.D₂ (.up ℤ) (n - 1) n) = _
    rw [comp_add, L.ι_D₁, L.ι_D₂,
      L.d₁_eq (.up ℤ) (i₁' := a) (by simp) b n hab,
      L.d₂_eq (.up ℤ) (a - 1) (i₂' := b + 1) (by simp) n (by dsimp; omega)]
    simp [ComplexShape.ε₁, ComplexShape.ε₂]
  have hshift (c : ℤ) (hc : c + b = n) :
      (h.hom (a + 1) c).f b ≫ L.ιTotal (.up ℤ) c b n hc =
        (h.hom (a + 1) a).f b ≫ L.ιTotal (.up ℤ) a b n hab := by
    have : c = a := by omega
    subst c
    rfl
  rw [hdL, hshift]
  simp only [comp_add, hsign, Units.neg_smul]
  rw [← (h.hom a (a - 1)).comm_assoc b (b + 1) _]
  dsimp at h₀b
  rw [h₀b]
  simp only [add_comp, Category.assoc]
  simp only [comp_neg, Linear.comp_units_smul]
  abel

/-- 横の同じ鎖ホモトピーを、非有界直和全複体の鎖ホモトピーとして読む。 -/
def totalHorizontalHomotopy :
    Homotopy (HomologicalComplex₂.total.map f (.up ℤ))
      (HomologicalComplex₂.total.map g (.up ℤ)) where
  hom := totalHorizontalComponent (fun a => h.hom a (a - 1))
  zero := totalHorizontalComponent_shape _
  comm n := by
    rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel n (n + 1)),
      prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (n - 1) n)]
    exact totalHorizontalComponent_comm h n

/-- 横の鎖ホモトピー同値は、同じ二つの射を用いる全複体の鎖ホモトピー同値を誘導する。 -/
def totalHorizontalHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.total (.up ℤ)) (L.total (.up ℤ)) where
  hom := HomologicalComplex₂.total.map e.hom (.up ℤ)
  inv := HomologicalComplex₂.total.map e.inv (.up ℤ)
  homotopyHomInvId := by
    simpa only [HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.map_id] using
      totalHorizontalHomotopy e.homotopyHomInvId
  homotopyInvHomId := by
    simpa only [HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.map_id] using
      totalHorizontalHomotopy e.homotopyInvHomId

end SerrePositivity.HomologicalAlgebra
