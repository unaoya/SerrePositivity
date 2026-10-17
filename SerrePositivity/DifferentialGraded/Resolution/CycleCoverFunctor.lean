module
public import SerrePositivity.DifferentialGraded.Resolution.CycleCover

/-! # 全cycle被覆のchain mapに関する厳密な関手性

## 概要
全cycle被覆のchain mapに関する厳密な関手性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {K L M : Complex A}

def complexMapCycle (f : K ⟶ L) (n : ℤ) (z : complexCycles A K n) : complexCycles A L n :=
  ⟨f.f n z.val, by
    have h := congrArg (fun g => g z.val) (f.comm n (n + 1))
    change L.d n (n + 1) (f.f n z.val) = 0
    change L.d n (n + 1) (f.f n z.val) = f.f (n + 1) (K.d n (n + 1) z.val) at h
    rw [z.property, map_zero] at h
    exact h⟩

lemma complexMapCycle_id (n : ℤ) (z : complexCycles A K n) :
    complexMapCycle A (𝟙 K) n z = z := Subtype.ext rfl

lemma complexMapCycle_comp (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) (z : complexCycles A K n) :
    complexMapCycle A (f ≫ g) n z = complexMapCycle A g n (complexMapCycle A f n z) :=
  Subtype.ext rfl

lemma complexSphereMap_mapCycle (f : K ⟶ L) (n : ℤ) (z : complexCycles A K n) :
    complexSphereMap A n z ≫ f = complexSphereMap A n (complexMapCycle A f n z) := by
  apply (complexSphereHomEquiv A L n).injective
  apply Subtype.ext
  change (complexSphereCycle A n (complexSphereMap A n z ≫ f)).val = _
  rw [complexSphereCycle_comp]
  have hz : (complexSphereCycle A n (complexSphereMap A n z)).val = z.val :=
    congrArg Subtype.val ((complexSphereHomEquiv A K n).apply_symm_apply z)
  have hf : (complexSphereCycle A n
      (complexSphereMap A n (complexMapCycle A f n z))).val = (complexMapCycle A f n z).val :=
    congrArg Subtype.val ((complexSphereHomEquiv A L n).apply_symm_apply (complexMapCycle A f n z))
  change _ = (complexSphereCycle A n (complexSphereMap A n (complexMapCycle A f n z))).val
  rw [hf]
  change f.f n (complexSphereCycle A n (complexSphereMap A n z)).val = f.f n z.val
  rw [hz]

def complexCycleCoverMap (f : K ⟶ L) : complexCycleCover A K ⟶ complexCycleCover A L :=
  Sigma.desc (fun j : ComplexCycleIndex A K =>
    complexCycleCoverLift A L j.1 (complexMapCycle A f j.1 j.2))

lemma complexCycleCoverLift_map (f : K ⟶ L) (n : ℤ) (z : complexCycles A K n) :
    complexCycleCoverLift A K n z ≫ complexCycleCoverMap A f =
      complexCycleCoverLift A L n (complexMapCycle A f n z) := Sigma.ι_comp_desc _ _

lemma complexCycleCoverMap_π (f : K ⟶ L) :
    complexCycleCoverMap A f ≫ complexCycleCoverπ A L = complexCycleCoverπ A K ≫ f := by
  apply Sigma.hom_ext
  intro j
  change complexCycleCoverLift A K j.1 j.2 ≫ _ = complexCycleCoverLift A K j.1 j.2 ≫ _
  rw [← Category.assoc, complexCycleCoverLift_map, complexCycleCoverLift_π,
    ← Category.assoc, complexCycleCoverLift_π, complexSphereMap_mapCycle]

lemma complexCycleCoverMap_id (K : Complex A) : complexCycleCoverMap A (𝟙 K) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro j
  change complexCycleCoverLift A K j.1 j.2 ≫ _ = complexCycleCoverLift A K j.1 j.2 ≫ _
  rw [complexCycleCoverLift_map, complexMapCycle_id, Category.comp_id]

lemma complexCycleCoverMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    complexCycleCoverMap A (f ≫ g) = complexCycleCoverMap A f ≫ complexCycleCoverMap A g := by
  apply Sigma.hom_ext
  intro j
  change complexCycleCoverLift A K j.1 j.2 ≫ _ = complexCycleCoverLift A K j.1 j.2 ≫ _
  rw [complexCycleCoverLift_map, complexMapCycle_comp, ← Category.assoc,
    complexCycleCoverLift_map, complexCycleCoverLift_map]

end SerrePositivity.DifferentialGraded
