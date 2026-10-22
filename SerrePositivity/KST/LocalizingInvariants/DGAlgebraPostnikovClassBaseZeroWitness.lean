module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeWitness

/-!
概要：零 class 標的での実経路を、元の共通底上の元の class 標的へ持ち上げる。
方針：実底変更の普遍性で両端を同定し、恒等係数の同型で元へ戻す。
規約：底への定数射影を保持する。使われ方：標準 class への経路の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (s : ℤ) (b : P ⟶ postnikov R B n) {W : Mon (Complex R)}
  (a : W ⟶ P)
  (u v : W ⟶ SquareZero.algebra P
    (bimoduleRestrict b (postnikovShiftedLayerBimodule R B n hn s)))
  (hu : u ≫ SquareZero.projection _ _ = a) (hv : v ≫ SquareZero.projection _ _ = a)
  (w : Path.Witness R
    (u ≫ (SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn s) ≫
      postnikovClassToZeroBase R B n hn s))
    (v ≫ (SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn s) ≫
      postnikovClassToZeroBase R B n hn s)))
  (hw : w.hom ≫ Path.map R (SquareZero.projection _ _) =
    (a ≫ (b ≫ postnikovTransition R B n 0 hn)) ≫ Path.diagonal R (postnikov R B 0))

/-- 追加の経路存在を仮定せず、同じ零標的の経路を元の class 標的へ戻す。 -/
def postnikovClassBaseZeroWitness : Path.Witness R u v := by
  let q := b ≫ postnikovTransition R B n 0 hn
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s
  let z := SquareZero.baseChangeMap b (postnikovShiftedLayerBimodule R B n hn s) ≫
    postnikovClassToZeroBase R B n hn s
  let e := postnikovClassBaseZeroIso R B P n hn s b
  have hmap : e.hom ≫ SquareZero.baseChangeMap q N = z :=
    postnikovClassBaseZeroIso_map R B P n hn s b
  have huz : (u ≫ z) ≫ SquareZero.projection _ _ = a ≫ q := by
    rw [← hmap]
    simp only [Category.assoc]
    rw [SquareZero.baseChangeMap_projection, ← Category.assoc e.hom,
      postnikovClassBaseZeroIso_projection, ← Category.assoc u, hu]
  have hvz : (v ≫ z) ≫ SquareZero.projection _ _ = a ≫ q := by
    rw [← hmap]
    simp only [Category.assoc]
    rw [SquareZero.baseChangeMap_projection, ← Category.assoc e.hom,
      postnikovClassBaseZeroIso_projection, ← Category.assoc v, hv]
  have hmu : SquareZero.baseChangeLift q N a (u ≫ z) huz = u ≫ e.hom := by
    apply SquareZero.baseChange_hom_ext q N
    · rw [SquareZero.baseChangeLift_projection, Category.assoc,
        postnikovClassBaseZeroIso_projection, hu]
    · rw [SquareZero.baseChangeLift_map, Category.assoc, hmap]
  have hmv : SquareZero.baseChangeLift q N a (v ≫ z) hvz = v ≫ e.hom := by
    apply SquareZero.baseChange_hom_ext q N
    · rw [SquareZero.baseChangeLift_projection, Category.assoc,
        postnikovClassBaseZeroIso_projection, hv]
    · rw [SquareZero.baseChangeLift_map, Category.assoc, hmap]
  let t := SquareZero.baseChangeWitness q N a (u ≫ z) (v ≫ z) huz hvz w hw
  refine ⟨t.hom ≫ Path.map R e.inv, ?_, ?_⟩
  · rw [Category.assoc, Path.map_source, ← Category.assoc, t.source_eq, hmu,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, Path.map_target, ← Category.assoc, t.target_eq, hmv,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma postnikovClassBaseZeroWitness_projection :
    (postnikovClassBaseZeroWitness R B P n hn s b a u v hu hv w hw).hom ≫
      Path.map R (SquareZero.projection _ _) = a ≫ Path.diagonal R P := by
  change (_ ≫ Path.map R (postnikovClassBaseZeroIso R B P n hn s b).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovClassBaseZeroIso_inv_projection,
    SquareZero.baseChangeWitness_relative]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
