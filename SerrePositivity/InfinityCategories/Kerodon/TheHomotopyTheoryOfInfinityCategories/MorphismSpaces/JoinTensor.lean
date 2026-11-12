module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：join の左因子と単体集合の直積の比較。
方針：join の切断の左側に直積の第一成分を制限する。
規約：右因子上では第一成分を忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、§7.1.8（Tag 02X8） の slice と関手単体集合の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace Join

/-- 概要：先頭の r 個の頂点を全頂点の区間へ含める順序写像。
方針：値を変えずに有限集合の大きさを広げる。
規約：空区間も許す。
使われ方：Kerodon §4.6.6（Tag 04HY） の join と直積の比較。 -/
def prefixIncl (n r : ℕ) (hr : r ≤ n) : Fin r →o Fin n where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
  monotone' := fun _ _ h ↦ h

/-- 概要：空区間を補った直積の単体は補った単体どうしの組と同値。
方針：空区間では一点性、非空区間では直積の成分を使う。
規約：頂点数 r で添字付ける。
使われ方：Kerodon §4.6.6（Tag 04HY） の直積の join への移送。 -/
def augTensorEquiv (A B : SSet.{u}) : (r : ℕ) → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (A ⊗ B) r ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B r
  | 0 =>
    { toFun := fun _ ↦ (PUnit.unit, PUnit.unit)
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by rcases x with ⟨⟨⟩, ⟨⟩⟩; rfl }
  | _ + 1 => Equiv.refl _

/-- 概要：補った直積の単体の同値は順序写像による引き戻しと可換。
方針：空区間を分け、非空区間では直積の単体作用を計算する。
規約：空の始域への写像も含む。
使われ方：Kerodon §4.6.6（Tag 04HY） の比較射の自然性。 -/
lemma augTensorEquiv_symm_augMap (A B : SSet.{u}) {r s : ℕ} (α : Fin r →o Fin s)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A s) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (A ⊗ B) α ((augTensorEquiv A B s).symm (a, b)) =
      (augTensorEquiv A B r).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A α a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap B α b) := by
  cases r with
  | zero => rfl
  | succ r =>
    cases s with
    | zero => exact Fin.elim0 (α 0)
    | succ s => rfl

/-- 概要：補った直積の単体の同値は第一因子の射と可換。
方針：空区間と非空区間で計算する。
規約：第二因子は恒等射。
使われ方：Kerodon §4.6.6（Tag 04HY） の比較射のパラメーターへの自然性。 -/
lemma augTensorEquiv_symm_augHomLeft {A A' : SSet.{u}} (f : A ⟶ A') (B : SSet.{u})
    (r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (f ▷ B) r ((augTensorEquiv A B r).symm (a, b)) =
      (augTensorEquiv A' B r).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f r a, b) := by
  cases r <;> rfl

/-- 概要：切断の先頭への制限と全体の単体の引き戻しは可換。
方針：切断の左写像と先頭の包含の合成を比較する。
規約：α の始域・終域は頂点数で添字付ける。
使われ方：Kerodon §4.6.6（Tag 04HY） の join の比較射の自然性。 -/
lemma augMap_prefix_leftMap (A : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (r : ℕ) (hr : r ≤ n) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (prefixIncl n r hr) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (prefixIncl m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α r)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A α a) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp]
  congr 1

/-- 概要：直積と join の単体から、左因子だけを直積にした join の単体を作る。
方針：join の切断を保ち、第一成分を左区間へ制限する。
規約：右因子の単体はそのまま保つ。
使われ方：Kerodon Construction 4.6.6.4（Tag 04J1） の比較。 -/
def tensorLeftSimplex (A B C : SSet.{u}) (n : ℕ)
    (a : A _⦋n⦌) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex B C n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (A ⊗ B) C n :=
  ⟨s.1, (augTensorEquiv A B s.1.val).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (prefixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) a, s.2.1), s.2.2⟩

/-- 概要：左因子の直積への比較は単体作用と可換。
方針：同じ切断を使い、先頭への制限の可換性を適用する。
規約：任意の次数の単体を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY） の比較射の自然性。 -/
lemma tensorLeftSimplex_naturality (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (a : A _⦋n⦌) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex B C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap (A ⊗ B) C α (tensorLeftSimplex A B C n a s) =
      tensorLeftSimplex A B C m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A α a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap B C α s) := by
  rcases s with ⟨ℓ, b, c⟩
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap, tensorLeftSimplex]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rw [augTensorEquiv_symm_augMap, augMap_prefix_leftMap]
    rfl
  · rfl

end Join

/-- 概要：直積と join を、左因子だけの直積と join へ比較する射。
方針：各次数で切断の左側へ第一成分を制限する。
規約：右因子上では第一成分を忘れる。
使われ方：Kerodon Construction 4.6.6.4（Tag 04J1）、§7.1.8（Tag 02X8） の slice と関手の比較。 -/
def joinTensorLeft (A B C : SSet.{u}) : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (A ⊗ B) C where
  app n := ↾fun s ↦ Join.tensorLeftSimplex A B C n.unop.len s.1 s.2
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    exact (Join.tensorLeftSimplex_naturality A B C α.unop.toOrderHom a s).symm

/-- 概要：join と直積の比較は直積の第一因子の射に自然。
方針：切断上の引き戻しと射の自然性を各成分で比較する。
規約：join の二つの因子は固定する。
使われ方：Kerodon Construction 4.6.6.4（Tag 04J1） の比較の自然性。 -/
lemma joinTensorLeft_naturality {A A' : SSet.{u}} (f : A ⟶ A') (B C : SSet.{u}) :
    (f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) ≫ joinTensorLeft A' B C =
      joinTensorLeft A B C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ▷ B) (𝟙 C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  rcases s with ⟨ℓ, b, c⟩
  change Join.tensorLeftSimplex A' B C n (f.app (Opposite.op ⦋n⦌) a) ⟨ℓ, b, c⟩ =
    ⟨ℓ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (f ▷ B) ℓ.val ((Join.augTensorEquiv A B ℓ.val).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt)) a, b)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 C) (n + 1 - ℓ.val) c⟩
  dsimp only [Join.tensorLeftSimplex]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rw [Join.augTensorEquiv_symm_augHomLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_naturality]
    rfl
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id C _ c).symm

/-- 概要：join の右包含は単射。
方針：切断零の直和の右成分を取る。
規約：任意の単体集合を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY） の関手単体集合の制限の inner fibration 性。 -/
instance joinInr_mono (A B : SSet.{u}) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h).2)

/-- 概要：join の左包含は単射。
方針：右区間が空の直和の左成分を取る。
規約：任意の単体集合を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY） の錐の頂点の固定。 -/
instance joinInl_mono (A B : SSet.{u}) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h).2)

/-- 概要：join と直積の比較は左包含と可換。
方針：切断が全頂点の場合、先頭への制限は恒等となる。
規約：左因子には直積の両成分を残す。
使われ方：Kerodon §4.6.6（Tag 04HY） の slice の比較の射影。 -/
lemma joinTensorLeft_inl (A B C : SSet.{u}) :
    (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B C) ≫ joinTensorLeft A B C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (A ⊗ B) C := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  change Join.tensorLeftSimplex A B C n a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl b) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl (a, b)
  unfold Join.tensorLeftSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap A (Join.prefixIncl (n + 1) (n + 1) _) a, b) = (a, b)
    have hp : Join.prefixIncl (n + 1) (n + 1) (by rfl) = OrderHom.id := rfl
    rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_id]
  · rfl

/-- 概要：join と直積の比較は右包含上で直積の第一成分を忘れる。
方針：切断零の分岐を計算する。
規約：右因子はそのまま保つ。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定された右図式。 -/
lemma joinTensorLeft_inr (A B C : SSet.{u}) :
    (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B C) ≫ joinTensorLeft A B C =
      CartesianMonoidalCategory.snd A C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (A ⊗ B) C := rfl

/-- 概要：一点を第一因子にした比較でその一点を忘れると第二射影。
方針：切断ごとに左成分の第二射影を計算する。
規約：一点は標準零単体を使う。
使われ方：Kerodon §4.6.6（Tag 04HY） の比較射の零単体の計算。 -/
lemma joinTensorLeft_unit (B C : SSet.{u}) :
    joinTensorLeft (Δ[0] : SSet.{u}) B C ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) B) (𝟙 C) =
      CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨⟨r, hr⟩, b, c⟩⟩
  cases r with
  | zero => cases b; rfl
  | succ r =>
    change (⟨⟨r + 1, hr⟩, b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 C) (n + 1 - (r + 1)) c⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex B C n) =
      ⟨⟨r + 1, hr⟩, b, c⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
