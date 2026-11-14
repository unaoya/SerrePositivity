module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveListCutStep
/-!
概要：切断の区間添字と任意の指定中間次数の結合則を比較する。
方針：有限区間の所属を直接比較し、元の dg 合成の結合則を使う。
規約：元の同じ実 cochain を使う。使われ方：tensor 候補の合成項と全次元 HA の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveGradedCompose_assoc {w x y z : D} {p q r a b n : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y q) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z r)
    (ha : p + q = a) (hb : q + r = b) (hn : a + r = n) (hn' : p + b = n) :
    _root_.SerrePositivity.DifferentialGraded.compose R h (compose R g f ha) hn = _root_.SerrePositivity.DifferentialGraded.compose R (compose R h g hb) f hn' := by
  subst a b
  exact _root_.SerrePositivity.DifferentialGraded.compose_assoc R f g h hn
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveCutInterval_lower_upper {n : ℕ} (I : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    (I.filter (i ≤ ·)).filter (· ≤ j) = (I.filter (· ≤ j)).filter (i ≤ ·) := by
  ext x
  simp only [Finset.mem_filter]
  tauto
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveCutInterval_upper_upper {n : ℕ} (I : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (I.filter (i ≤ ·)).filter (j ≤ ·) = I.filter (j ≤ ·) := by
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_trans hij h.2⟩, h.2⟩⟩
/-- 同じ実切断合成を左右の区間へ照合する。 -/
lemma dgNerveCutInterval_lower_lower {n : ℕ} (I : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (I.filter (· ≤ j)).filter (· ≤ i) = I.filter (· ≤ i) := by
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, le_trans h.2 hij⟩, h.2⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
