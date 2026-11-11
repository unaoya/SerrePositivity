module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixReplacement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanCandidateData

/-! # 後続置換による右辺の型付き比較

概要：生の右辺の変化を、指定した Hom の線形式へ異種等号で移す。
方針：置換族の自己評価、合成・符号倍・差の異種等号の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：実境界の Q・A の微分式への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 端点と次数の等式を伴う異種等号は整数単位の符号倍を保つ。 -/
lemma gradedHom_units_smul_heq {X Y X' Y' : D} {k l : ℤ}
    (hx : X = X') (hy : Y = Y') (hk : k = l) (e : ℤˣ)
    (f : GradedHom R X Y k) (g : GradedHom R X' Y' l) (hfg : HEq f g) :
    HEq (e • f) (e • g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq hfg
  rfl

namespace SimplexData

/-- 後続成分の置換後の一点追加集合の右辺を、指定 Hom 内の線形式と比較する。 -/
lemma spanOnePrefixRhs_replaceFixed_suffix_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
    (hzero : s.spanSuffixHom = 0)
    {X P Y : D} (hx : s.obj a = X) (hp : s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = P)
    (hy : s.obj (Fin.last (n + 3)) = Y)
    {l : ℤ} (hl : -(n : ℤ) = l)
    (q' : GradedHom R P Y l) (r : GradedHom R X Y l) (p : GradedHom R X P 0)
    (hq : HEq q q') (hr : HEq (s.spanOnePrefixRhs a ha) r)
    (hleg : HEq (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) p) :
    HEq ((s.replaceFixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega) q).spanOnePrefixRhs a ha)
      (r - ((n : ℤ) + 1).negOnePow • compose R q' p (zero_add l)) := by
  have H := s.spanOnePrefixRhs_replace_suffix
    (s.fixedHomFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega) q) a ha
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_self, hzero, sub_zero] at H
  have hrdeg : -(n : ℤ) - 1 + 1 = l := by omega
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) hx hp hy rfl hl hrdeg
    _ _ q' p hq hleg (by omega) (zero_add l)
  have hs := gradedHom_units_smul_heq (R := R) hx hy hrdeg ((n : ℤ) + 1).negOnePow _ _ hc
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq (A := R) hx hy hrdeg _ _ _ _ hr hs
  have hv := (sub_eq_iff_eq_add.mp H).trans (show
    -(((n : ℤ) + 1).negOnePow • compose R q (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) (by omega)) +
      s.spanOnePrefixRhs a ha =
      s.spanOnePrefixRhs a ha -
        ((n : ℤ) + 1).negOnePow • compose R q (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) (by omega) by abel)
  exact (heq_of_eq hv).trans ht

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData (spanOnePrefixRhs_replaceFixed_suffix_heq)


end SimplexData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
