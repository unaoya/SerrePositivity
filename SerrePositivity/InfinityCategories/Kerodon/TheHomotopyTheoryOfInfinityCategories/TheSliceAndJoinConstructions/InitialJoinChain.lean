module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.AugmentedNerve

/-!
概要：点と nerve の join 型の単体を WithInitial の射列へ戻す。
方針：切断より前を新しい始対象、後を元の射列とし、またぐ射は始対象の射とする。
規約：ここでは次数ごとの射列を構成し、単体的自然性は別に検証する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の nerve と点の join の同定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：切断以後の頂点を join の後半の添字へ移す。
方針：元の添字から切断の頂点数を引く。
規約：切断以後にあるという条件を明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の後半の評価。 -/
def initialJoinTailIndex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i : Fin (n + 1)) (hi : ¬ i.val < s.1.val) : Fin (n + 1 - s.1.val) :=
  ⟨i.val - s.1.val, by have := i.isLt; omega⟩

/-- 概要：join の単体の頂点を WithInitial の対象として読む。
方針：切断より前は新しい始対象、それ以降は後半の射列の対象を使う。
規約：後半が空の場合も元の圏の対象を選ばない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点と nerve の比較射。 -/
def initialJoinObj {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i : Fin (n + 1)) : WithInitial C :=
  if hi : i.val < s.1.val then .star
  else .of (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2 (initialJoinTailIndex s i hi))

/-- 概要：切断より前の頂点は新しい始対象である。
方針：頂点の定義の前半を評価する。
規約：切断の条件を明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の端点の移送。 -/
lemma initialJoinObj_star {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i : Fin (n + 1)) (hi : i.val < s.1.val) :
    initialJoinObj s i = WithInitial.star := by simp [initialJoinObj, hi]

/-- 概要：切断以後の頂点は後半の元の対象の包含である。
方針：頂点の定義の後半を評価する。
規約：後半の添字には切断を引く。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の端点の移送。 -/
lemma initialJoinObj_of {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i : Fin (n + 1)) (hi : ¬ i.val < s.1.val) :
    initialJoinObj s i = WithInitial.of (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2 (initialJoinTailIndex s i hi)) := by
  simp [initialJoinObj, hi]

/-- 概要：join の単体の二頂点間の射を WithInitial の射として読む。
方針：始点が新しい始対象なら一意な射、両端が後半なら元の射列の射を使う。
規約：後半から新しい始対象への射は添字の単調性で除く。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点と nerve の比較射。 -/
def initialJoinMap {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    {i j : Fin (n + 1)} (h : i ≤ j) : initialJoinObj s i ⟶ initialJoinObj s j :=
  if hi : i.val < s.1.val then
    eqToHom (initialJoinObj_star s i hi) ≫ WithInitial.starInitial.to _
  else
    have hj : ¬ j.val < s.1.val := fun hj => hi (lt_of_le_of_lt h hj)
    eqToHom (initialJoinObj_of s i hi) ≫
      (WithInitial.incl : C ⥤ WithInitial C).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap s.2.2 (Nat.sub_le_sub_right h s.1.val)) ≫
      eqToHom (initialJoinObj_of s j hj).symm

/-- 概要：join から読んだ同じ頂点の射は恒等射である。
方針：切断の前後で場合分けし、後半では nerve の恒等射の評価を使う。
規約：全ての切断を扱い、空の後半も許す。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の関手法則。 -/
lemma initialJoinMap_id {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i : Fin (n + 1)) : initialJoinMap s (le_refl i) = 𝟙 (initialJoinObj s i) := by
  by_cases hi : i.val < s.1.val
  · have he := initialJoinObj_star s i hi
    have : Subsingleton (initialJoinObj s i ⟶ initialJoinObj s i) := by
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _
  · simp only [initialJoinMap, dite_eq_right hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap_id]
    change eqToHom (initialJoinObj_of s i hi) ≫
      𝟙 (WithInitial.of (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2 (initialJoinTailIndex s i hi))) ≫
      eqToHom (initialJoinObj_of s i hi).symm = 𝟙 (initialJoinObj s i)
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- 概要：join から読んだ射は三頂点の合成を保つ。
方針：切断をまたぐ場合は始対象の一意性、後半では nerve の合成の評価を使う。
規約：添字は昇順で、合成も同じ向きとする。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の関手法則。 -/
lemma initialJoinMap_comp {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    initialJoinMap s (hij.trans hjk) = initialJoinMap s hij ≫ initialJoinMap s hjk := by
  by_cases hi : i.val < s.1.val
  · have he : initialJoinObj s i = WithInitial.star := by simp [initialJoinObj, hi]
    have : Subsingleton (initialJoinObj s i ⟶ initialJoinObj s k) := by
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _
  · have hj : ¬ j.val < s.1.val := fun h => hi (lt_of_le_of_lt hij h)
    have hk : ¬ k.val < s.1.val := fun h => hj (lt_of_le_of_lt hjk h)
    simp only [initialJoinMap, dite_eq_right hi, dite_eq_right hj]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Functor.map_comp_assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap_comp]

/-- 概要：点と nerve の join 型の単体は WithInitial の射列を定める。
方針：前半の新しい始対象と後半の元の射列を、始対象の射でつなぐ。
規約：この定義は次数ごとの構成で、単体的自然性はまだ含めない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の nerve と点の join の同定。 -/
def initialJoinChain {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    ComposableArrows (WithInitial C) n where
  obj := initialJoinObj s
  map f := initialJoinMap s (leOfHom f)
  map_id i := initialJoinMap_id s i
  map_comp f g := initialJoinMap_comp s (leOfHom f) (leOfHom g)

/-- 概要：構成した射列の新しい始対象の頂点は元の切断より前の頂点である。
方針：前半は始対象の定義、後半は WithInitial の二つの構成子の相異を使う。
規約：端の切断も含めて全頂点で同値を述べる。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較の逆関係。 -/
lemma initialJoinChain_star_iff {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (n + 1)) :
    (initialJoinChain s).obj i = WithInitial.star ↔ i.val < s.1.val := by
  change initialJoinObj s i = WithInitial.star ↔ _
  by_cases hi : i.val < s.1.val
  · simp [initialJoinObj, hi]
  · simp [initialJoinObj, hi]

/-- 概要：join から構成した射列の切断は元の join の切断に等しい。
方針：各頂点が切断より前である条件を新しい始対象への一致で比較する。
規約：後半が空の場合も含み、対象の非空性を要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の nerve と join の比較の逆関係。 -/
lemma initialNerveCut_initialJoinChain {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut (initialJoinChain s) = s.1.val := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut_le _) (by have := s.1.isLt; omega)
  intro i
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerve_lt_cut_iff _ i).trans (initialJoinChain_star_iff s i)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
