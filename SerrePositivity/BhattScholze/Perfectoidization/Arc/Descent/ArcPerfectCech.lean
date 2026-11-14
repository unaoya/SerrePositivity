module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.Cech.BaseChange
public import Mathlib.FieldTheory.Perfect

/-!
## 概要
完全標数 p 環の増大 Čech 余脈体の各項の完全性。
## 方針
逆 Frobenius を広い押し出しの普遍性から作る。
## 規約
通常の余脈体を使い、その項が零環になる場合も含める。
## 使われ方
BM18 Proposition 4.8 の構造層の適用で各項に Tor 消滅を使う。
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SerrePositivity.Cech

set_option backward.isDefEq.respectTransparency false

/-- 通常の Čech 余脈体の各項は完全環（BM18 Proposition 4.8 の構造層への適用）。 -/
theorem cechConerve_perfectRing (p : ℕ) [Fact p.Prime]
    (f : Arrow CommRingCat.{u}) (hp : (p : f.left) = 0)
    [PerfectRing f.left p] [PerfectRing f.right p] (n : SimplexCategory) :
    PerfectRing (f.cechConerve.obj n) p := by
  let a : Fin (n.len + 1) → (f.left ⟶ f.right) := fun _ => f.hom
  let W := widePushout f.left (fun _ : Fin (n.len + 1) => f.right) a
  change PerfectRing W p
  rcases subsingleton_or_nontrivial W with hs | ht
  · exact ⟨⟨fun _ _ _ => hs.elim _ _, fun x => ⟨0, hs.elim _ _⟩⟩⟩
  let head := WidePushout.head a
  let leg (i : Fin (n.len + 1)) := WidePushout.ι a i
  let : Nontrivial f.left := head.hom.domain_nontrivial
  let : Nontrivial f.right := (leg 0).hom.domain_nontrivial
  have hB : (p : f.right) = 0 := by rw [← map_natCast f.hom.hom, hp, map_zero]
  have hW : (p : W) = 0 := by rw [← map_natCast head.hom, hp, map_zero]
  let : CharP f.left p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
  let : CharP f.right p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hB
  let : CharP W p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hW
  let rA := (frobeniusEquiv f.left p).symm.toRingHom
  let rB := (frobeniusEquiv f.right p).symm.toRingHom
  let ff := CommRingCat.ofHom (frobenius W p)
  have hr (i : Fin (n.len + 1)) :
      a i ≫ CommRingCat.ofHom rB ≫ leg i = CommRingCat.ofHom rA ≫ head := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (leg i) (rB (f.hom x)) = head (rA x)
    rw [show rB (f.hom x) = f.hom (rA x) from
      (f.hom.hom.map_frobeniusEquiv_symm p x).symm]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (WidePushout.arrow_ι a i)) (rA x)
  let r : W ⟶ W := WidePushout.desc (CommRingCat.ofHom rA ≫ head)
    (fun i => CommRingCat.ofHom rB ≫ leg i) hr
  have hf (i : Fin (n.len + 1)) : leg i ≫ ff = CommRingCat.ofHom (frobenius f.right p) ≫ leg i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (map_pow (leg i).hom x p).symm
  have hf₀ : head ≫ ff = CommRingCat.ofHom (frobenius f.left p) ≫ head := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (map_pow head.hom x p).symm
  have hrA : CommRingCat.ofHom (frobenius f.left p) ≫ CommRingCat.ofHom rA = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (frobeniusEquiv f.left p).left_inv
  have hAr : CommRingCat.ofHom rA ≫ CommRingCat.ofHom (frobenius f.left p) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (frobeniusEquiv f.left p).right_inv
  have hrB : CommRingCat.ofHom (frobenius f.right p) ≫ CommRingCat.ofHom rB = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (frobeniusEquiv f.right p).left_inv
  have hBr : CommRingCat.ofHom rB ≫ CommRingCat.ofHom (frobenius f.right p) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (frobeniusEquiv f.right p).right_inv
  have h₁ : ff ≫ r = 𝟙 W := by
    apply WidePushout.hom_ext
    · intro i
      rw [← Category.assoc, hf, Category.assoc]
      change CommRingCat.ofHom (frobenius f.right p) ≫ WidePushout.ι a i ≫
        WidePushout.desc _ _ hr = _
      rw [WidePushout.ι_desc, ← Category.assoc, hrB, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, hf₀, Category.assoc]
      change CommRingCat.ofHom (frobenius f.left p) ≫ WidePushout.head a ≫
        WidePushout.desc _ _ hr = _
      rw [WidePushout.head_desc, ← Category.assoc, hrA, Category.id_comp, Category.comp_id]
  have h₂ : r ≫ ff = 𝟙 W := by
    apply WidePushout.hom_ext
    · intro i
      rw [← Category.assoc]
      change (WidePushout.ι a i ≫ WidePushout.desc _ _ hr) ≫ ff = _
      rw [WidePushout.ι_desc]
      change (CommRingCat.ofHom rB ≫ leg i) ≫ ff = _
      rw [Category.assoc, hf, ← Category.assoc, hBr, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc]
      change (WidePushout.head a ≫ WidePushout.desc _ _ hr) ≫ ff = _
      rw [WidePushout.head_desc]
      change (CommRingCat.ofHom rA ≫ head) ≫ ff = _
      rw [Category.assoc, hf₀, ← Category.assoc, hAr, Category.id_comp, Category.comp_id]
  have hinj : Function.LeftInverse r.hom ff.hom :=
    fun x => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h₁) x
  have hsurj : Function.RightInverse r.hom ff.hom :=
    fun x => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h₂) x
  exact ⟨⟨hinj.injective, hsurj.surjective⟩⟩

end SerrePositivity.Cech

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 8.10" (partial := component) "BM18 の経路 B（BS-W12）の B1〜B5 は本体。組み立て B6 は ⑥ の BS17 Thm 4.1 (i) 待ち ／ 11-10 更新"] _root_.SerrePositivity.Cech.cechConerve_perfectRing
