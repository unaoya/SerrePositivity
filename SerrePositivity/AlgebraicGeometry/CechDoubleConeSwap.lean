module

public import SerrePositivity.AlgebraicGeometry.CechDoubleConeSwapTerm
public import Mathlib.Tactic.Abel

/-!
概要：実際の可換四角から作る二つの二重 cone を、符号付きで交換する複体の同型。
方針：既存の成分の交換を微分と照合し、二回の交換の恒等則を使う。
規約：四角形の実際の cochain map と可換性を保持する。
使われ方：共通細分での射影四角形の全複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {A B A' B' : CochainComplex (ModuleCat.{u} R) ℕ}
variable (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
variable (h : f ≫ b = a ≫ g)

set_option backward.isDefEq.respectTransparency false in
/-- 二重 cone の符号付きの交換は、二つの微分と可換。 -/
theorem cechDoubleConeSwapTerm_differential (n : ℕ) :
    (cechDoubleConeSwapTerm f g a b (n + 1)).comp
      (cechRefinementConeDifferential (cechRefinementCone A B f)
        (cechRefinementCone A' B' g) (cechRefinementConeMap a b h) n) =
      (cechRefinementConeDifferential (cechRefinementCone A A' a)
        (cechRefinementCone B B' b) (cechRefinementConeMap f g h.symm) n).comp
          (cechDoubleConeSwapTerm f g a b n) := by
  have hd (C D : CochainComplex (ModuleCat.{u} R) ℕ) (m : C ⟶ D) (k : ℕ) :
      (cechRefinementCone C D m).d k (k + 1) =
        ModuleCat.ofHom (cechRefinementConeDifferential C D m k) := by
    dsimp only [cechRefinementCone, CochainComplex.of]
    rw [CochainComplex.of_d]
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
    change (-(-((f.f 0).hom x)), (-((a.f 0).hom x), -(-((A.d 0 1).hom x)))) =
      ((f.f 0).hom x, (-((a.f 0).hom x), -(-((A.d 0 1).hom x))))
    simp only [neg_neg]
  | succ n =>
    cases n with
    | zero =>
      change ((-((g.f 0).hom x.1 + (b.f 0).hom x.2.1),
          -(-((B.d 0 1).hom x.2.1 + (f.f 1).hom x.2.2))),
        (-(-((A'.d 0 1).hom x.1) + (a.f 1).hom x.2.2),
          -(-((A.d 1 2).hom x.2.2)))) =
        (((b.f 0).hom (-x.2.1) + (g.f 0).hom (-x.1),
          -((B.d 0 1).hom (-x.2.1)) + (f.f 1).hom x.2.2),
        (-((A'.d 0 1).hom (-x.1) + (a.f 1).hom x.2.2),
          -(-((A.d 1 2).hom x.2.2))))
      simp only [map_neg, neg_neg, neg_add]
      congr 2 <;> abel
    | succ n =>
      simp only [cechDoubleConeSwapTerm, cechRefinementConeDifferential]
      rw [hd A' B' g (n + 1), hd A B f (n + 2),
        hd B B' b (n + 1), hd A A' a (n + 2)]
      simp only [cechRefinementConeMap, cechRefinementConeMapTerm,
        cechRefinementConeDifferential]
      change ((-((B'.d n (n + 1)).hom x.1.1 + (g.f (n + 1)).hom x.1.2 +
          (b.f (n + 1)).hom x.2.1),
          -(-((B.d (n + 1) (n + 2)).hom x.2.1 + (f.f (n + 2)).hom x.2.2))),
        (-(-((A'.d (n + 1) (n + 2)).hom x.1.2) + (a.f (n + 2)).hom x.2.2),
          -(-((A.d (n + 2) (n + 3)).hom x.2.2)))) =
        (((B'.d n (n + 1)).hom (-x.1.1) + (b.f (n + 1)).hom (-x.2.1) +
          (g.f (n + 1)).hom (-x.1.2),
          -((B.d (n + 1) (n + 2)).hom (-x.2.1)) + (f.f (n + 2)).hom x.2.2),
        (-((A'.d (n + 1) (n + 2)).hom (-x.1.2) + (a.f (n + 2)).hom x.2.2),
          -(-((A.d (n + 2) (n + 3)).hom x.2.2))))
      simp only [map_neg, neg_neg, neg_add]
      congr 2 <;> abel

set_option backward.isDefEq.respectTransparency false in
/-- 実際の二つの二重 cone の間の、符号付きの余鎖写像。 -/
def cechDoubleConeSwapMap :
    cechRefinementCone (cechRefinementCone A B f) (cechRefinementCone A' B' g)
        (cechRefinementConeMap a b h) ⟶
      cechRefinementCone (cechRefinementCone A A' a) (cechRefinementCone B B' b)
        (cechRefinementConeMap f g h.symm) :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (cechDoubleConeSwapTerm f g a b n)) (by
    intro n
    simp only [cechRefinementCone, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact (cechDoubleConeSwapTerm_differential f g a b h n).symm)

/-- 同じ可換四角の二つの二重 cone は、実際の複体として同型。 -/
def cechDoubleConeSwapIso :
    cechRefinementCone (cechRefinementCone A B f) (cechRefinementCone A' B' g)
        (cechRefinementConeMap a b h) ≅
      cechRefinementCone (cechRefinementCone A A' a) (cechRefinementCone B B' b)
        (cechRefinementConeMap f g h.symm) where
  hom := cechDoubleConeSwapMap f g a b h
  inv := cechDoubleConeSwapMap a b f g h.symm
  hom_inv_id := by
    ext n x
    exact LinearMap.congr_fun (cechDoubleConeSwapTerm_involutive f g a b n) x
  inv_hom_id := by
    ext n x
    exact LinearMap.congr_fun (cechDoubleConeSwapTerm_involutive a b f g n) x

end SerrePositivity.AlgebraicGeometry
