module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinear

/-! # 右 pinched 線形成分族の引き戻し

概要：有限集合上単射なら像で評価し、潰れる高次成分は零とする線形写像を作る。
方針：非空集合と次数の添字を保ち、単射性の場合分けで関手の法則を示す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形単体の面と退化の構成。
この段階では方程式を課す前の成分族を扱う。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：単調写像に沿う線形成分族の A 線形な引き戻し。
方針：各部分集合上で単射なら像の成分を使い、非単射なら零を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形模型の面・退化。 -/
def pullback {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n →ₗ[A] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y m where
  toFun f i := if hi : Set.InjOn α (i.val.1 : Set (Fin (m + 1))) then
    f.component (i.val.1.image α) i.val.2 (i.property.1.image α)
      (by rw [Finset.card_image_of_injOn hi]; exact i.property.2)
    else 0
  map_add' f g := by
    funext i
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.add_apply]
    split_ifs
    · rfl
    · exact (zero_add _).symm
  map_smul' c f := by
    funext i
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · rfl
    · exact (smul_zero c).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pullback)


/-- 概要：単射な部分集合上の引き戻し成分は像の集合の成分。
方針：引き戻しの単射分岐を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：面写像の成分の計算。 -/
lemma pullback_component_of_inj {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    (pullback α f).component J k hJ hk =
      f.component (J.image α) k (hJ.image α) (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pullback, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left hi]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pullback_component_of_inj)


/-- 概要：非単射な部分集合上の引き戻し成分は零。
方針：引き戻しの非単射分岐を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：退化写像の潰れた高次成分の計算。 -/
lemma pullback_component_of_not_inj {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (hi : ¬ Set.InjOn α (J : Set (Fin (m + 1)))) :
    (pullback α f).component J k hJ hk = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pullback, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hi]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pullback_component_of_not_inj)


/-- 概要：成分族の恒等写像による引き戻しは元に戻る。
方針：全ての部分集合上で単射であり、像の集合が変わらないことを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形模型の単体的恒等則。 -/
lemma pullback_id {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) : pullback OrderHom.id f = f := by
  funext i
  simp only [pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, LinearMap.coe_mk, AddHom.coe_mk,
    OrderHom.id_coe, Set.injOn_id, dite_true]
  congr 1
  apply Subtype.ext
  exact Prod.ext Finset.image_id rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pullback_id)


/-- 概要：線形成分族の引き戻しは反変に合成する。
方針：最初の写像の単射性とその像上の次の写像の単射性で場合分けする。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形模型の単体的合成則。 -/
lemma pullback_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1))
    (β : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) :
    pullback α (pullback β f) = pullback (β.comp α) f := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (pullback α (pullback β f)).component J k hJ hk =
    (pullback (β.comp α) f).component J k hJ hk
  by_cases hi : Set.InjOn α (J : Set (Fin (l + 1)))
  · have hiff : Set.InjOn (β.comp α) (J : Set (Fin (l + 1))) ↔
        Set.InjOn β ((J.image α) : Set (Fin (m + 1))) := by
      simpa only [Finset.coe_image, OrderHom.comp_coe] using hi.comp_iff (g := β)
    by_cases hiβ : Set.InjOn β ((J.image α) : Set (Fin (m + 1)))
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pullback, LinearMap.coe_mk, AddHom.coe_mk,
        dite_eq_left hi, dite_eq_left hiβ, dite_eq_left (hiff.mpr hiβ)]
      congr 1
      apply Subtype.ext
      exact Prod.ext Finset.image_image rfl
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pullback, LinearMap.coe_mk, AddHom.coe_mk,
        dite_eq_left hi, dite_eq_right hiβ, dite_eq_right (mt hiff.mp hiβ)]
  · have hnot : ¬ Set.InjOn (β.comp α) (J : Set (Fin (l + 1))) := by
      intro h
      apply hi
      intro a ha b hb hab
      exact h ha hb (congrArg β hab)
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pullback, LinearMap.coe_mk, AddHom.coe_mk,
      dite_eq_right hi, dite_eq_right hnot]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (pullback_comp)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
