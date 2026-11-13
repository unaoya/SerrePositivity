module

public import SerrePositivity.AlgebraicGeometry.CechRefinementCone

/-!
概要：複体の射の可換な四角から、細分を測る cone の射を作る。
方針：零項では左側の射、以後は右側と左側の射の直積を使う。
規約：cone は負一次から自然数に移したもの。
使われ方：共通細分の二重複体で、もう一方の Čech 微分との可換性を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {A B A' B' A'' B'' : CochainComplex (ModuleCat.{u} R) ℕ}
variable {f : A ⟶ B} {g : A' ⟶ B'} {h : A'' ⟶ B''}

/-- cone の各項に可換四角の成分を適用する。 -/
def cechRefinementConeMapTerm (a : A ⟶ A') (b : B ⟶ B') :
    ∀ n, cechRefinementConeTerm A B n →ₗ[R] cechRefinementConeTerm A' B' n
  | 0 => (a.f 0).hom
  | n + 1 => ((b.f n).hom.comp (LinearMap.fst R _ _)).prod
      ((a.f (n + 1)).hom.comp (LinearMap.snd R _ _))

/-- 可換四角の成分は cone の微分と可換。 -/
theorem cechRefinementConeMapTerm_differential (a : A ⟶ A') (b : B ⟶ B')
    (hab : f ≫ b = a ≫ g) (n : ℕ) :
    (cechRefinementConeMapTerm a b (n + 1)).comp
        (cechRefinementConeDifferential A B f n) =
      (cechRefinementConeDifferential A' B' g n).comp
        (cechRefinementConeMapTerm a b n) := by
  have ha (i : ℕ) (x : A.X i) :
      (a.f (i + 1)).hom ((A.d i (i + 1)).hom x) =
        (A'.d i (i + 1)).hom ((a.f i).hom x) := by
    exact (congrArg (fun m ↦ m.hom x) (a.comm i (i + 1))).symm
  have hb (i : ℕ) (x : B.X i) :
      (b.f (i + 1)).hom ((B.d i (i + 1)).hom x) =
        (B'.d i (i + 1)).hom ((b.f i).hom x) := by
    exact (congrArg (fun m ↦ m.hom x) (b.comm i (i + 1))).symm
  have hs (i : ℕ) (x : A.X i) :
      (b.f i).hom ((f.f i).hom x) = (g.f i).hom ((a.f i).hom x) :=
    congrArg (fun m : A ⟶ B' ↦ (m.f i).hom x) hab
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
    change ((b.f 0).hom ((f.f 0).hom x), (a.f 1).hom (-(A.d 0 1).hom x)) =
      ((g.f 0).hom ((a.f 0).hom x), -(A'.d 0 1).hom ((a.f 0).hom x))
    simp only [map_neg, ha, hs]
  | succ n =>
    change ((b.f (n + 1)).hom ((B.d n (n + 1)).hom x.1 + (f.f (n + 1)).hom x.2),
      (a.f (n + 2)).hom (-(A.d (n + 1) (n + 2)).hom x.2)) =
      ((B'.d n (n + 1)).hom ((b.f n).hom x.1) +
        (g.f (n + 1)).hom ((a.f (n + 1)).hom x.2),
        -(A'.d (n + 1) (n + 2)).hom ((a.f (n + 1)).hom x.2))
    simp only [map_add, map_neg, ha, hb, hs]

/-- 可換四角が誘導する cone の射。 -/
def cechRefinementConeMap (a : A ⟶ A') (b : B ⟶ B') (hab : f ≫ b = a ≫ g) :
    cechRefinementCone A B f ⟶ cechRefinementCone A' B' g :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (cechRefinementConeMapTerm a b n)) (by
    intro n
    simp only [cechRefinementCone, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact (cechRefinementConeMapTerm_differential a b hab n).symm)

/-- cone の項への写像は合成を保つ。 -/
theorem cechRefinementConeMapTerm_comp (a : A ⟶ A') (b : B ⟶ B')
    (a' : A' ⟶ A'') (b' : B' ⟶ B'') (n : ℕ) :
    (cechRefinementConeMapTerm a' b' n).comp (cechRefinementConeMapTerm a b n) =
      cechRefinementConeMapTerm (a ≫ a') (b ≫ b') n := by
  cases n <;> rfl

/-- cone の項への恒等写像。 -/
theorem cechRefinementConeMapTerm_id (n : ℕ) :
    cechRefinementConeMapTerm (𝟙 A) (𝟙 B) n = LinearMap.id := by
  cases n <;> rfl

/-- cone の項への零写像。 -/
theorem cechRefinementConeMapTerm_zero (n : ℕ) :
    cechRefinementConeMapTerm (0 : A ⟶ A') (0 : B ⟶ B') n = 0 := by
  cases n <;> rfl

end SerrePositivity.AlgebraicGeometry
