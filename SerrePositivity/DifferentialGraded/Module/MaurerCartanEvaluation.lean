module
public import SerrePositivity.DifferentialGraded.Module.Postcomposition
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanHomMap
/-!
概要：右 dg 加群の Maurer–Cartan 要素を各評価複体と全次数の作用へ送る。
方針：主 Hom の合成・微分の成分式と、次数一要素の符号付き自然性を使う。
規約：係数圏だけの Small 仮定で、全加群圏の Small は要求しない。
使われ方：coherent 図式の bar 微分を加えた実 dg 加群。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

variable (M : RightModule R D) (θ : (moduleHom R D M M).X 1)
  (hθ : (moduleHom R D M M).d 1 2 θ +
    compose R (x := M) (y := M) (z := M) θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

include hθ in
lemma moduleMaurerCartan_evaluation (x : D) :
    δ 1 2 ((moduleHomπ R D M M x).f 1 θ) +
      ((moduleHomπ R D M M x).f 1 θ).comp
        ((moduleHomπ R D M M x).f 1 θ) (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  have h := congrArg ((moduleHomπ R D M M x).f 2) hθ
  simpa only [map_add, map_zero, differential, moduleHomElement_d_π,
    moduleHomCompose_π] using h

lemma moduleMaurerCartan_action (x y : Dᵒᵖ) (p : ℤ) (a : GradedHom R x y p) :
    ((M.map x y).f p a).comp ((moduleHomπ R D M M y.unop).f 1 θ) rfl +
      (p + 1).negOnePow • (((moduleHomπ R D M M x.unop).f 1 θ).comp
        ((M.map x y).f p a) (by omega : 1 + p = p + 1)) = 0 := by
  apply Cochain.ext
  intro i j hij
  have h := congrArg (fun c : Cochain (M.obj x) (M.obj y) (1 + p) =>
    c.v i j (by omega)) (moduleHomElement_naturality R D 1 θ x y p a)
  have hs : (p + 1).negOnePow = -p.negOnePow := by
    rw [Int.negOnePow_add]
    simp
  simp only [one_mul, Cochain.units_smul_v] at h
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega)] at h
  rw [Cochain.add_v, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ _ i (i + 1) j rfl (by omega), hs]
  simpa only [Units.smul_def, Units.val_neg, neg_zsmul, ← sub_eq_add_neg, Cochain.zero_v] using
    sub_eq_zero.mpr h

end SerrePositivity.DifferentialGraded
