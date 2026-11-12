module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex

/-!
# 標準 DK 成分模型の単体的構造

概要：標準 chain map 方程式の解を単体的加群とし、N4 の小さい Hom と自然同型にする。
方針：全次数の線形同値を介して引き戻しを移し、台の成分族が通常の引き戻しとなることを証明する。
規約：Mathlib Γ との同定と豊穣合成はこのファイルでは仮定しない。
使われ方：HA 1.3.1.12–1.3.1.14、Kerodon 2.5.6（Tag 00QQ） の全次数で自然な Hom の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準方程式の解を単調写像に沿って線形に引き戻す。
方針：N4 の引き戻しを標準座標の同値で挟む。
規約：後続の成分計算で通常の有限集合の像による作用に一致させる。
使われ方：HA 1.3.1.12 の標準 DK 単体の面と退化。 -/
def standardPullback {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n →ₗ[R] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y m :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y m).toLinearMap.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n).symm.toLinearMap)

/-- 概要：標準単体の引き戻しの成分族は通常の有限集合の像による引き戻しである。
方針：符号変換の自然性を使い、二重の符号変換を消す。
規約：単射でない正次数成分は零になる。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の具体的な単体的構造の確認。 -/
lemma standardPullback_val {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    (standardPullback α f).val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f.val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData f.val)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_involutive]

/-- 概要：標準単体の引き戻しは恒等写像を保つ。
方針：台の成分族に移して既存の恒等則を使う。
規約：解の証明の一意性は部分型の外延性で処理する。
使われ方：HA 1.3.1.12 の単体的恒等則。 -/
lemma standardPullback_id {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    standardPullback OrderHom.id f = f := by
  apply Subtype.ext
  rw [standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_id]

/-- 概要：標準単体の引き戻しは反変に合成する。
方針：台の成分族に移して既存の合成則を使う。
規約：全ての単調写像に対する等式。
使われ方：HA 1.3.1.12 の単体的合成則。 -/
lemma standardPullback_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1))
    (β : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    standardPullback α (standardPullback β f) = standardPullback (β.comp α) f := by
  apply Subtype.ext
  rw [standardPullback_val, standardPullback_val, standardPullback_val]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_comp α β f.val

/-- 概要：標準座標への同値は引き戻しと可換である。
方針：引き戻しを挟む二つの同値のうち一対を消す。
規約：全次数での自然性を線形写像の値として述べる。
使われ方：HA 1.3.1.12 の単体的加群の自然同型。 -/
lemma standardPullback_equiv {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n) :
    standardPullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α f) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y m
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n f))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- 概要：標準の chain map 方程式の解を小さい単体的 R 加群とする。
方針：各次数の解と具体的な線形引き戻し、その恒等・合成則を使う。
規約：値の宇宙は係数環の宇宙 u。
使われ方：HA 1.3.1.13、Kerodon 2.5.6（Tag 00QQ） の DK Hom の標準成分模型。 -/
def standardModule (x y : D) : SimplicialObject (ModuleCat.{u} R) where
  obj n := ModuleCat.of R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n.unop.len)
  map f := ModuleCat.ofHom (standardPullback f.unop.toOrderHom)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    exact standardPullback_id f
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (standardPullback_comp g.unop.toOrderHom f.unop.toOrderHom s).symm

/-- 概要：N4 の小さい Hom の加群と標準 DK 成分の加群は単体的に自然同型である。
方針：各次数の線形同値を射にし、引き戻しとの可換性と両逆則を添える。
規約：次数ごとの同値だけでなく全ての退化も含む自然同型。
使われ方：HA 1.3.1.12 の実際の写像空間との比較。 -/
def standardModuleIso (x y : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModule (R := R) x y ≅ standardModule (R := R) x y where
  hom :=
    { app := fun n ↦ ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len).toLinearMap
      naturality := by
        intro m n α
        apply ConcreteCategory.hom_ext
        intro f
        exact (standardPullback_equiv α.unop.toOrderHom f).symm }
  inv :=
    { app := fun n ↦ ModuleCat.ofHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len).symm.toLinearMap
      naturality := by
        intro m n α
        apply ConcreteCategory.hom_ext
        intro f
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len).injective
        change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len).symm
            (standardPullback α.unop.toOrderHom f)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α.unop.toOrderHom
              ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y m.unop.len).symm f))
        rw [LinearEquiv.apply_symm_apply, ← standardPullback_equiv,
          LinearEquiv.apply_symm_apply] }
  hom_inv_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len).symm_apply_apply f
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x y n.unop.len).apply_symm_apply f

/-- 概要：標準 DK 成分模型の台単体集合。
方針：標準方程式の単体的加群の後に忘却関手を合成する。
規約：まだ Mathlib の Γ と同一の定義とはしない。
使われ方：HA 1.3.1.13 の単体的 Hom の標準座標による表現。 -/
def standardHomSpace (x y : D) : SSet.{u} :=
  standardModule (R := R) x y ⋙ forget (ModuleCat.{u} R)

/-- 概要：N4 の小さい Hom と標準 DK 座標の単体集合は同型である。
方針：単体的加群の自然同型を忘却関手で送る。
規約：単体集合の実際の射と逆射を持つ同型。
使われ方：HA 1.3.1.12 の写像空間と標準成分模型の比較。 -/
def homSpaceStandardIso (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpace (R := R) x y ≅ standardHomSpace (R := R) x y :=
  Functor.isoWhiskerRight (standardModuleIso (R := R) x y) (forget (ModuleCat.{u} R))

open SSet.modelCategoryQuillen in
/-- 概要：標準 DK 成分模型の単体集合は Kan 複体である。
方針：N4 の小さい Hom の Kan 性を自然同型の逆射に沿って移す。
規約：単体的群の一般の Kan 定理は仮定しない。
使われ方：HA 1.3.1.14、Kerodon 2.5.9.2（Tag 00SE） の標準 Hom の局所 Kan 性。 -/
instance standardHomSpaceKan (x y : D) : SSet.KanComplex (standardHomSpace (R := R) x y) :=
  HomotopicalAlgebra.isFibrant_of_fibration (homSpaceStandardIso (R := R) x y).inv

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
