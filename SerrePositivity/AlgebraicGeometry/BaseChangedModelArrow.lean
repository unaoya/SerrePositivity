module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
概要：模型間の基底上の射を、実際の段の底変換模型間の射へ移す合成の法則。
方針：pullback lift の二射影で恒等・合成・一致を判定する。
規約：係数段の射に単射性・平坦性の仮定を置かない。
使われ方：G2 の逆・cocycle の式を有限段へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S X Y Z : Scheme.{u}}

/-- 固定模型間の基底上の射を、段の実際の底変換模型間の射へ移す。 -/
def baseChangedModelArrow (γ : B ⟶ S) (p : X ⟶ S) (q : Y ⟶ S)
    (l : X ⟶ Y) (hl : l ≫ q = p) : pullback γ p ⟶ pullback γ q :=
  pullback.lift (pullback.fst γ p) (pullback.snd γ p ≫ l)
    (by rw [Category.assoc, hl]; exact pullback.condition)

/-- 基底座標の保持。 -/
@[reassoc (attr := simp)] theorem baseChangedModelArrow_fst
    (γ : B ⟶ S) (p : X ⟶ S) (q : Y ⟶ S) (l : X ⟶ Y) (hl : l ≫ q = p) :
    baseChangedModelArrow γ p q l hl ≫ pullback.fst γ q = pullback.fst γ p := by
  simp [baseChangedModelArrow]

/-- 固定模型への射影と元の射の可換式。 -/
@[reassoc (attr := simp)] theorem baseChangedModelArrow_snd
    (γ : B ⟶ S) (p : X ⟶ S) (q : Y ⟶ S) (l : X ⟶ Y) (hl : l ≫ q = p) :
    baseChangedModelArrow γ p q l hl ≫ pullback.snd γ q = pullback.snd γ p ≫ l := by
  simp [baseChangedModelArrow]

/-- 実際の底変換は恒等射を保つ。 -/
@[simp] theorem baseChangedModelArrow_id (γ : B ⟶ S) (p : X ⟶ S) :
    baseChangedModelArrow γ p p (𝟙 _) (Category.id_comp p) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- 実際の底変換は射の合成を保つ。 -/
theorem baseChangedModelArrow_comp (γ : B ⟶ S)
    (p : X ⟶ S) (q : Y ⟶ S) (r : Z ⟶ S)
    (l : X ⟶ Y) (hl : l ≫ q = p) (n : Y ⟶ Z) (hn : n ≫ r = q) :
    baseChangedModelArrow γ p q l hl ≫ baseChangedModelArrow γ q r n hn =
      baseChangedModelArrow γ p r (l ≫ n) (by rw [Category.assoc, hn, hl]) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- 実際の段の二射の一致は、固定模型への射影の一致で判定できる。 -/
theorem baseChangedModelArrow_eq_iff (γ : B ⟶ S) (p : X ⟶ S) (q : Y ⟶ S)
    (l r : X ⟶ Y) (hl : l ≫ q = p) (hr : r ≫ q = p) :
    baseChangedModelArrow γ p q l hl = baseChangedModelArrow γ p q r hr ↔
      pullback.snd γ p ≫ l = pullback.snd γ p ≫ r := by
  constructor
  · intro h
    simpa only [baseChangedModelArrow_snd] using congrArg (fun z ↦ z ≫ pullback.snd γ q) h
  · intro h
    apply pullback.hom_ext
    · simp
    · simpa only [baseChangedModelArrow_snd] using h

end SerrePositivity.AlgebraicGeometry
