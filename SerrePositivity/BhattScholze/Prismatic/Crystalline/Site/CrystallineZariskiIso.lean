module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteZariski
public import SerrePositivity.CommutativeAlgebra.Localization.AwayEquivalence
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 同型による結晶 Zariski 被覆の移送

## 概要
厚化の同型と被覆族の同型で主開被覆の条件は変わらない。

## 方針
厚化の同型を代数同型として読み、分冪イデアルの像と局所化条件を移す。

## 規約
各脚の可換正方形を明示する。小さい模型の選択に依存しない。

## 使われ方
Berthelot III.4、Stacks 07HN。小さい結晶サイトの関手での被覆保存。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}
namespace CrysOver

/-- 厚化の同型の台の代数同型。 -/
def isoAlgEquiv {X Y : CrysOver p γ R κ} (e : X ≅ Y) : X.B ≃ₐ[k] Y.B :=
  { e.hom.toAlgHom with
    invFun := e.inv.toAlgHom
    left_inv := fun x => congrArg (fun a : X ⟶ X => a.toAlgHom x) e.hom_inv_id
    right_inv := fun y => congrArg (fun a : Y ⟶ Y => a.toAlgHom y) e.inv_hom_id }

/-- 厚化の同型は分冪イデアルを像として一致させる。 -/
theorem ideal_map_iso {X Y : CrysOver p γ R κ} (e : X ≅ Y) :
    X.JB.map e.hom.toAlgHom.toRingHom = Y.JB := by
  apply le_antisymm e.hom.dp.ideal_comp
  have hc : e.hom.toAlgHom.toRingHom.comp e.inv.toAlgHom.toRingHom = RingHom.id Y.B :=
    congrArg (fun a : Y ⟶ Y => a.toAlgHom.toRingHom) e.inv_hom_id
  calc
    Y.JB = (Y.JB.map e.inv.toAlgHom.toRingHom).map e.hom.toAlgHom.toRingHom := by
      rw [Ideal.map_map, hc, Ideal.map_id]
    _ ≤ X.JB.map e.hom.toAlgHom.toRingHom := Ideal.map_mono e.inv.dp.ideal_comp

/-- 可換な族の同型は結晶主開被覆条件を保つ。 -/
theorem IsZariskiFamily.of_iso {ι : Type u} [Finite ι]
    {X X' : CrysOver p γ R κ} {Y Y' : ι → CrysOver p γ R κ}
    {f : ∀ i, X ⟶ Y i} {f' : ∀ i, X' ⟶ Y' i}
    (hf : IsZariskiFamily Y f) (e : X ≅ X') (v : ∀ i, Y i ≅ Y' i)
    (he : ∀ i, f i ≫ (v i).hom = e.hom ≫ f' i) : IsZariskiFamily Y' f' := by
  obtain ⟨b, hb, hl⟩ := hf
  refine ⟨fun i => e.hom.toAlgHom (b i), ?_, ?_⟩
  · have hr : e.hom.toAlgHom.toRingHom '' Set.range b =
        Set.range (fun i => e.hom.toAlgHom (b i)) := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
    rw [← hr, ← Ideal.map_span, hb, Ideal.map_top]
  · intro i
    letI : Algebra X.B (Y i).B := (f i).toAlgHom.toRingHom.toAlgebra
    letI : Algebra X'.B (Y' i).B := (f' i).toAlgHom.toRingHom.toAlgebra
    letI : IsLocalization.Away (b i) (Y i).B := (hl i).1
    have hs : (v i).hom.toAlgHom.toRingHom.comp (f i).toAlgHom.toRingHom =
        (f' i).toAlgHom.toRingHom.comp e.hom.toAlgHom.toRingHom :=
      congrArg (fun a : X ⟶ Y' i => a.toAlgHom.toRingHom) (he i)
    refine ⟨SerrePositivity.CommutativeAlgebra.Localization.away_of_equivalence
      (isoAlgEquiv e).toRingEquiv (isoAlgEquiv (v i)).toRingEquiv
      (fun x => DFunLike.congr_fun hs x) (b i), ?_⟩
    calc
      (Y' i).JB = (Y i).JB.map (v i).hom.toAlgHom.toRingHom := (ideal_map_iso (v i)).symm
      _ = (X.JB.map (f i).toAlgHom.toRingHom).map (v i).hom.toAlgHom.toRingHom := by rw [(hl i).2]
      _ = (X.JB.map e.hom.toAlgHom.toRingHom).map (f' i).toAlgHom.toRingHom := by
        rw [Ideal.map_map, Ideal.map_map, hs]
      _ = X'.JB.map (f' i).toAlgHom.toRingHom := by rw [ideal_map_iso e]
end CrysOver
end SerrePositivity.BhattScholze.Prismatic
