module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Normalized
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.PerfectComplex.SupPropertyComap

/-! # 証明済みの根の塔の長さの完備化への係数制限

Noether 局所基底・素数・極大イデアル内の座標から構成した正規化長さを、
p 進完備化上の加群へ制限する。長さの加法性は非完備な塔の証明を使い、
完備化や perfectoidization の引用によって長さの法則を補わない。
Paper 層には依存しない。
-/

@[expose] public section
universe u
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

/-- 証明済みの塔の正規化長さを、p 進完備化への係数制限で測る具体的な長さ。 -/
noncomputable def completedNormalizedLength :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  completedLengthOf A t p (normalizedLength A t p ht)

/-- 完備化上の加群の長さは、非完備な塔へ係数制限した三段階の数値関数。 -/
@[simp] theorem completedNormalizedLength_len (M : Type u) [AddCommGroup M]
    [Module (CompletedTower A t p) M] :
    (completedNormalizedLength A t p ht).len M =
      (letI := Module.compHom M (algebraMap (Tower A t p) (CompletedTower A t p))
       towerLengthFun A t p M) := rfl

/-- 完備化への係数制限後も、有限生成部分加群の長さの上限として計算できる。 -/
theorem completedNormalizedLength_hasSup : (completedNormalizedLength A t p ht).HasSup :=
  (normalizedLength_hasSup A t p ht).comap
    (algebraMap (Tower A t p) (CompletedTower A t p)) _
    (towerMaxIdeal_map_completed A t p).le

/-- 直接の係数制限と完備化経由の係数制限は、具体的な長さについて同じ値を返す。 -/
theorem completedNormalizedLength_restrictScalars
    (C : Type u) [CommRing C] [Algebra (Tower A t p) C]
    [Algebra (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]
    (M : Type u) [AddCommGroup M] [Module C M] :
    (letI := Module.compHom M (algebraMap (Tower A t p) C)
     (normalizedLength A t p ht).len M) =
    (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
     (completedNormalizedLength A t p ht).len M) :=
  completedLengthOf_restrictScalars A t p (normalizedLength A t p ht) C M

end SerrePositivity.RootTowerLength
