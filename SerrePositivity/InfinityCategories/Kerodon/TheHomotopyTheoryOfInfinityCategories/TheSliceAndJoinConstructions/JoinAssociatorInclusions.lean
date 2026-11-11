module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorMaps

/-!
概要：join の結合同型と固定面の包含の可換式。
方針：補った単体の和表示で空の因子を計算し、三つの区間の共通表示で検出する。
規約：結合同型の順方向は左括弧から右括弧。各包含の向きを明示する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の反復 slice の固定面と射影の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：右因子の包含は和表示で左の頂点数零となる。
方針：全頂点数を分け、join の包含の定義を計算する。
規約：頂点数零の補った単体も含む。
使われ方：Kerodon §4.3.5（Tag 017V） の右の固定面の再結合。 -/
lemma augmentedJoinSumEquiv_inr (A B : SSet.{u}) (n : ℕ) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) n b) =
      (⟨⟨0, n, PUnit.unit, b⟩, by simp⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n) := by
  cases n with
  | zero => cases b; rfl
  | succ n => rfl

/-- 概要：左因子の包含は和表示で右の頂点数零となる。
方針：補った単体の包含を計算し、残りの頂点数が零になる等式を使う。
規約：空の右区間も唯一の補った単体で表す。
使われ方：Kerodon §4.3.5（Tag 017V） の左の固定面の再結合。 -/
lemma augmentedJoinSumEquiv_inl (A B : SSet.{u}) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv A B n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) n a) =
      (⟨⟨n, 0, a, PUnit.unit⟩, by simp⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B n) := by
  cases n with
  | zero => cases a; rfl
  | succ n =>
    apply Subtype.ext
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv, Prod.mk.eta, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl, eq_mpr_eq_cast,
      Equiv.coe_fn_mk, Sigma.mk.injEq, heq_eq_eq, tsub_self, true_and]
    have hp {U V W : Type u} (e : V = W) (x : U) (y : V) :
        HEq (x, cast e y) (x, y) := by cases e; rfl
    exact hp _ a PUnit.unit

/-- 概要：結合同型で移した単体の右表示は元の左表示に一致する。
方針：同型を二つの共通表示の全単射の合成に戻し、往復則を使う。
規約：構成済みの順方向の各次数の式。
使われ方：HTT §1.2.8 の結合同型の包含上の検出。 -/
lemma joinAssociator_hom_encoding (A B C : SSet.{u}) (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom.app _ s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C (n + 1) s := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C (n + 1) s)) = _
  exact Equiv.apply_symm_apply _ _

/-- 概要：後ろ二因子の固定面の包含は結合同型と可換。
方針：三つの区間の表示で検出し、最初の因子の頂点数が零であることを使う。
規約：始域は B⋆C、終域は A⋆(B⋆C)。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の反復 slice の固定された錐の面。 -/
lemma joinAssociator_rightPair (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) (𝟙 C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) (𝟙 C)).app _ s)) = _
  rw [joinAssociator_hom_encoding]
  rcases s with ⟨a, b, c⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C (n + 1)
      (⟨a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) a.val b,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 C) (n + 1 - a.val) c⟩) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
  apply Subtype.ext
  exact congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B a.val ↦
    (⟨q.val.1, q.val.2.1, n + 1 - a.val, q.val.2.2.1, q.val.2.2.2, c⟩ :
      Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c))
    (augmentedJoinSumEquiv_inr A B a.val b)

/-- 概要：前二因子の固定面の包含は結合同型と可換。
方針：三つの区間の表示で、最後の因子の空区間を比較する。
規約：始域は A⋆B、終域は A⋆(B⋆C)。
使われ方：HTT §1.2.8 の反復 slice の可変な前の面の計算。 -/
lemma joinAssociator_leftPair (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C).app _ s)) = _
  rw [joinAssociator_hom_encoding]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftJoinSumTripleEquiv A B C (n + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.augmentedJoinSumEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C) (n + 1) s)) = _
  rw [augmentedJoinSumEquiv_inl]
  rcases s with ⟨a, x, y⟩
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)
    (⟨a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 A) a.val x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B C) (n + 1 - a.val) y⟩)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
  apply Subtype.ext
  exact (congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex B C (n + 1 - a.val) ↦
    (⟨a.val, q.val.1, q.val.2.1, x, q.val.2.2.1, q.val.2.2.2⟩ :
      Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c))
    (augmentedJoinSumEquiv_inl B C (n + 1 - a.val) y)).symm

/-- 概要：後ろ二因子の包含を結合同型の逆で移すと左括弧での同じ固定面になる。
方針：順方向の可換式に逆を後合成する。
規約：始域は B⋆C、終域は (A⋆B)⋆C。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の再結合後の固定面の保持。 -/
lemma joinAssociator_inv_rightPair (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) (𝟙 C) := by
  rw [← joinAssociator_rightPair, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：前二因子の包含を結合同型の逆で移すと左括弧での左包含になる。
方針：順方向の可換式に逆を後合成する。
規約：始域は A⋆B。
使われ方：HTT §1.2.8 の再結合と前の面の制限。 -/
lemma joinAssociator_inv_leftPair (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C := by
  rw [← joinAssociator_leftPair, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：最後の因子の包含は結合同型で二重の右包含へ移る。
方針：後ろ二因子の包含の可換式をさらに最後の因子へ制限する。
規約：始域は C。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の反復 slice を元の図式へ制限する固定条件。 -/
lemma joinAssociator_last (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) (𝟙 C)
  simp only [Category.id_comp] at h
  rw [← h, Category.assoc, joinAssociator_rightPair]

/-- 概要：最初の因子の包含は結合同型の逆で二重の左包含へ移る。
方針：前二因子の包含の逆向きの可換式を最初の因子へ制限する。
規約：始域は A。
使われ方：HTT 4.2.4.1 の slice の可変頂点の射影の保持。 -/
lemma joinAssociator_inv_first (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) C := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B C)
  simp only [Category.id_comp] at h
  rw [← h, Category.assoc, joinAssociator_inv_leftPair]

/-- 概要：join の結合同型の逆も三因子の射に自然。
方針：順方向の自然性の両側に逆を合成し、同型の往復則で消去する。
規約：因子の射に追加の仮定はない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の反復 slice の順方向のパラメータ自然性。 -/
lemma joinAssociator_inv_naturality {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g h) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A' B' C').inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) h := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom).1
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 概要：中因子を空にした外側二因子の包含は結合同型と可換。
方針：三つの区間の表示で中因子の頂点数が零であることを両側から確認する。
規約：始域は A⋆C。中間の B の頂点は使わない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の展開した錐を元の図式へ制限する比較。 -/
lemma joinAssociator_outerPair (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) (𝟙 C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) (𝟙 C)).app _ s)) = _
  rw [joinAssociator_hom_encoding]
  rcases s with ⟨a, x, z⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.leftJoinTripleEncoding A B C (n + 1)
      (⟨a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) a.val x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 C) (n + 1 - a.val) z⟩) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightJoinTripleEncoding A B C (n + 1)
      (⟨a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 A) a.val x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B C) (n + 1 - a.val) z⟩)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
  apply Subtype.ext
  have hl := congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex A B a.val ↦
    (⟨q.val.1, q.val.2.1, n + 1 - a.val, q.val.2.2.1, q.val.2.2.2, z⟩ :
      Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c))
    (augmentedJoinSumEquiv_inl A B a.val x)
  have hr := congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinSumSimplex B C (n + 1 - a.val) ↦
    (⟨a.val, q.val.1, q.val.2.1, x, q.val.2.2.1, q.val.2.2.2⟩ :
      Σ a : ℕ, Σ b : ℕ, Σ c : ℕ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A a × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B b × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C c))
    (augmentedJoinSumEquiv_inr B C (n + 1 - a.val) z)
  exact hl.trans hr.symm

/-- 概要：外側二因子の包含を結合同型の逆で移すと左括弧の同じ面に一致する。
方針：外側二因子の順方向の可換式に逆を後合成する。
規約：中因子は空区間として扱う。
使われ方：HTT 4.2.4.1 の反復 slice の射影と図式の制限の一致。 -/
lemma joinAssociator_inv_outerPair (A B C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator A B C).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) (𝟙 C) := by
  rw [← joinAssociator_outerPair, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
