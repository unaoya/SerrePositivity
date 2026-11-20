module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TowerAffineMaps
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SequentialMittagLeffler

/-!
概要：Mittag–Leffler な群の逐次逆系の非可換 lim¹ は消滅する。
方針：部分群の右剰余類の像を比較し、twisted 方程式の塔の整合族を選ぶ。
規約：群の可換性・遷移の全射性・有限性は仮定しない。
使われ方：Goerss–Jardine VIII §1。塔の収束の lim¹ の制御。
-/

@[expose] public section
universe u
open CategoryTheory Opposite

namespace SerrePositivity.KST.Spectra.TowerLimOne
end SerrePositivity.KST.Spectra.TowerLimOne
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.TowerLimOne

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 右平行移動した像の包含は、元の像の逆向きの包含の下で等式になる。 -/
lemma translated_range_reverse {H K L : Type u} [Group H] [Group K] [Group L]
    (f : H →* L) (g : K →* L) (c d : L)
    (hfg : Set.range f ⊆ Set.range g)
    (hsub : Set.range (fun b ↦ g b * d) ⊆ Set.range (fun a ↦ f a * c)) :
    Set.range (fun a ↦ f a * c) ⊆ Set.range (fun b ↦ g b * d) := by
  obtain ⟨t, ht⟩ := hsub (show d ∈ Set.range (fun b ↦ g b * d) from ⟨1, by simp⟩)
  rintro z ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := hfg ⟨a * t⁻¹, rfl⟩
  refine ⟨b, ?_⟩
  change g b * d = f a * c
  change f t * c = d at ht
  rw [hb, ← ht]
  simp [map_mul, map_inv, mul_assoc]

variable (G : ℕ → Type u) [∀ n, Group (G n)] (q : ∀ n, G (n + 1) →* G n)

/-- 群の塔の像が最終的に安定する Mittag–Leffler 条件。 -/
def IsMittagLeffler : Prop := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.groupTower G q) ⋙ forget GrpCat).IsMittagLeffler

/-- 任意の矢に沿うアフィンな遷移の右平行移動表示。 -/
lemma affineTower_map_arrow (x : ∀ n, G n) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ∃ c : G j.unop, ∀ a : G i.unop,
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map f a = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q f) a * c := by
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower_map G q x j.unop i.unop (leOfHom f.unop)

/-- 元の群の像の安定性は twisted 方程式のアフィンな像の安定性を導く。 -/
lemma affineTower_isMittagLeffler (hG : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler G q) (x : ∀ n, G n) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).IsMittagLeffler := by
  apply (Functor.isMittagLeffler_iff_subset_range_comp _).2
  intro j
  obtain ⟨i, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp _).1 hG j
  refine ⟨i, f, fun {k} g ↦ ?_⟩
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower_map_arrow G q x f
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower_map_arrow G q x (g ≫ f)
  have hsub : Set.range ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map (g ≫ f)) ⊆
      Set.range ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map f) := by
    rw [Functor.map_comp]
    rintro _ ⟨a, rfl⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map g a, rfl⟩
  have hmap : ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map f) =
      ↾(fun a ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q f) a * c) := by
    ext a
    exact hc a
  have hmap' : ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map (g ≫ f)) =
      ↾(fun a ↦ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q (g ≫ f)) a * d) := by
    ext a
    exact hd a
  rw [hmap, hmap'] at hsub ⊢
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.translated_range_reverse (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q f)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q (g ≫ f)) c d (hf g) hsub

/-- Mittag–Leffler 条件の下で、任意の族を単位族へ送る twisted 作用がある。 -/
theorem exists_nullifier_of_mittagLeffler (hG : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler G q) (x : ∀ n, G n) :
    ∃ a : ∀ n, G n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q a x = 1 := by
  have : ∀ j, Nonempty ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).obj j) := fun j ↦ ⟨(1 : G j.unop)⟩
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_compatible_family (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower_isMittagLeffler G q hG x)
  refine ⟨a, funext fun n ↦ ?_⟩
  have hn := ha n
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower_step] at hn
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist]
  rw [← hn]
  simp [mul_assoc]

/-- Mittag–Leffler な群の塔では全ての lim¹ の元が基点になる。 -/
lemma mk_eq_point_of_mittagLeffler (hG : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler G q) (x : ∀ n, G n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk G q x = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point G q := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_nullifier_of_mittagLeffler G q hG x
  exact Quotient.sound ⟨a, ha⟩

/-- Mittag–Leffler な群の逐次逆系の非可換 lim¹ の消滅。 -/
theorem subsingleton_of_mittagLeffler (hG : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler G q) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne G q) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mk_eq_point_of_mittagLeffler G q hG x).trans
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mk_eq_point_of_mittagLeffler G q hG y).symm

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
