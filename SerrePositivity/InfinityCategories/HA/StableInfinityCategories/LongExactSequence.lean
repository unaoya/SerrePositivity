module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-! # Fiber 列の Hom 長完全列

概要：安定 quasicategory の fiber 列に Hom を適用すると、全整数次数の長完全列を得る。
方針：fiber 三角形の distinguished 性と加法的 Yoneda のホモロジー関手性を使う。
規約：六項部分列を全次数で扱い、二つの次数をまたぐ全ての位置の完全性を含める。
使われ方：S5 の長完全列、完全関手と導来 ∞ 圏の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated Pretriangulated.Opposite Opposite SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：fiber 列からホモトピー圏の三角形を得る。
方針：安定性で cofiber 列とみなして構成済みの三角形を使う。
規約：前加法構造と整数シフトは既存のもの。使われ方：Hom 長完全列の元の三角形。 -/
def fiberTriangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) : Triangle (hoFunctor.obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).1 ht)

/-- 概要：fiber 列の三角形は distinguished。
方針：安定性による cofiber 性から所属を得る。
規約：Mathlib の公開した三角構造の所属。使われ方：Homological functor の長完全列。 -/
lemma fiberTriangle_distinguished {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) :
    fiberTriangle t ht ∈ distTriang (hoFunctor.obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t).1 ht)

/-- 概要：固定始点からの Hom をアーベル群値の関手とする。
方針：加法的 coyoneda を使う。
規約：次数 n では Hom(W,A[n])。使われ方：共変 Hom 長完全列。 -/
abbrev fiberHomFunctor {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) : hoFunctor.obj X ⥤ AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op W)

/-- 概要：共変 Hom 関手の n 次の値の台集合は Hom(W,A[n])。
方針：tautological なシフト列の定義を計算する。
規約：任意の整数次数。使われ方：群値の列と通常の Hom 表示の照合。 -/
lemma fiberHomFunctor_shift_obj_type {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W A : hoFunctor.obj X) (n : ℤ) :
    ↥(((fiberHomFunctor W).shift n).obj A) =
      (W ⟶ (shiftFunctor (hoFunctor.obj X) n).obj A) := rfl

/-- 概要：共変 Hom のシフト関手の射への作用はシフトした射との後合成。
方針：加法的 coyoneda とシフト列の射を計算する。
規約：次数 n の通常の Hom 表示。使われ方：長完全列の非接続射を計算する。 -/
lemma fiberHomFunctor_shift_map_apply {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (n : ℤ) {A B : hoFunctor.obj X} (f : A ⟶ B)
    (x : W ⟶ (shiftFunctor (hoFunctor.obj X) n).obj A) :
    ((fiberHomFunctor W).shift n).map f x = x ≫ (shiftFunctor (hoFunctor.obj X) n).map f := rfl

/-- 概要：fiber 列の共変 Hom 長完全列の n 次の接続準同型。
方針：Homological functor の接続射を使う。
規約：Hom(W,C[n]) から Hom(W,A[n+1])。使われ方：隣接次数間の写像。 -/
def fiberHomConnecting {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ) :
    ((fiberHomFunctor W).shift n).obj (fiberTriangle t ht).obj₃ ⟶
      ((fiberHomFunctor W).shift (n + 1)).obj (fiberTriangle t ht).obj₁ :=
  (fiberHomFunctor W).homologySequenceδ (fiberTriangle t ht) n (n + 1) rfl

/-- 概要：共変 Hom の接続準同型は三角形の第三射の n 回シフトとの後合成。
方針：加法的 coyoneda の接続射の評価式を使う。
規約：整数シフトの加法の比較同型を明記。使われ方：長完全列の接続射の計算。 -/
lemma fiberHomConnecting_apply {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ)
    (x : W ⟶ (shiftFunctor (hoFunctor.obj X) n).obj (fiberTriangle t ht).obj₃) :
    fiberHomConnecting W t ht n x =
      x ≫ (shiftFunctor (hoFunctor.obj X) n).map (fiberTriangle t ht).mor₃ ≫
        (shiftFunctorAdd' (hoFunctor.obj X) 1 n (n + 1) (add_comm 1 n)).inv.app
          (fiberTriangle t ht).obj₁ :=
  preadditiveCoyoneda_homologySequenceδ_apply (fiberTriangle t ht) n (n + 1) rfl x

/-- 概要：共変 Hom の接続準同型は fiber 三角形間の射に関して自然。
方針：Homological functor の接続射の自然性を適用する。
規約：任意の三角形の射を入力できる。使われ方：長完全列の比較。
-/
lemma fiberHomConnecting_naturality {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence d)
    (φ : fiberTriangle t ht ⟶ fiberTriangle d hd) (n : ℤ) :
    ((fiberHomFunctor W).shift n).map φ.hom₃ ≫ fiberHomConnecting W d hd n =
      fiberHomConnecting W t ht n ≫ ((fiberHomFunctor W).shift (n + 1)).map φ.hom₁ :=
  (fiberHomFunctor W).homologySequenceδ_naturality φ n (n + 1) rfl

/-- 概要：共変 Hom 長完全列の連続した二次数の六項部分列。
方針：三角形の三射を Hom のシフト列へ送る。
規約：全ての n を動かすことで長完全列全体を表す。使われ方：アーベル群の完全列。 -/
def fiberHomSequence {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (fiberHomFunctor W).homologySequenceComposableArrows₅ (fiberTriangle t ht) n (n + 1) rfl

/-- 概要：fiber 列の共変 Hom 長完全列は全整数次数で完全。
方針：三角形の distinguished 性と coyoneda のホモロジー関手性を使う。
規約：六項の四つの内部位置を全て含む。使われ方：S5 の共変 Hom 長完全列。 -/
lemma fiberHomSequence_exact {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ) :
    (fiberHomSequence W t ht n).Exact :=
  (fiberHomFunctor W).homologySequenceComposableArrows₅_exact
    (fiberTriangle t ht) (fiberTriangle_distinguished t ht) n (n + 1) rfl

/-- 概要：固定終点への Hom を反変のアーベル群値関手とする。
方針：加法的 yoneda を使う。
規約：シフト列の n 次は Hom(A,W[n])。使われ方：反変 Hom 長完全列。 -/
abbrev fiberContravariantHomFunctor {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) : (hoFunctor.obj X)ᵒᵖ ⥤ AddCommGrpCat.{u} := preadditiveYoneda.obj W

/-- 概要：反変 Hom 関手の n 次の台集合は Hom(A,W[n])。
方針：加法的 yoneda のシフト列を計算する。
規約：任意の整数次数。使われ方：反変の列と通常の Hom 表示の照合。 -/
lemma fiberContravariantHomFunctor_shift_obj_type {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (W A : hoFunctor.obj X) (n : ℤ) :
    ↥(((fiberContravariantHomFunctor W).shift n).obj (op A)) =
      (A ⟶ (shiftFunctor (hoFunctor.obj X) n).obj W) := rfl

/-- 概要：反変 Hom 関手の射への作用は元の射との前合成。
方針：終点をシフトした加法的 yoneda の射を計算する。
規約：始点側の射を反対圏で扱う。使われ方：反変の長完全列の非接続射。 -/
lemma fiberContravariantHomFunctor_shift_map_apply {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (W : hoFunctor.obj X) (n : ℤ)
    {A B : hoFunctor.obj X} (f : A ⟶ B)
    (x : B ⟶ (shiftFunctor (hoFunctor.obj X) n).obj W) :
    ((fiberContravariantHomFunctor W).shift n).map f.op x = f ≫ x := rfl

/-- 概要：fiber 列の反変 Hom 長完全列の接続準同型。
方針：反対三角形の接続射を加法的 yoneda に送る。
規約：Hom(A,W[n]) から Hom(C,W[n+1])。使われ方：反変の列の隣接次数間の写像。 -/
def fiberContravariantHomConnecting {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ) :
    ((fiberContravariantHomFunctor W).shift n).obj (op (fiberTriangle t ht).obj₁) ⟶
      ((fiberContravariantHomFunctor W).shift (n + 1)).obj (op (fiberTriangle t ht).obj₃) :=
  (fiberContravariantHomFunctor W).homologySequenceδ
    ((triangleOpEquivalence (hoFunctor.obj X)).functor.obj (op (fiberTriangle t ht))) n (n + 1) rfl

/-- 概要：反変 Hom の接続準同型は第三射と一回シフトした元の合成。
方針：加法的 yoneda の反対三角形上の評価式を使う。
規約：整数シフトの比較同型を含める。使われ方：反変の長完全列の接続射を計算する。 -/
lemma fiberContravariantHomConnecting_apply {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ)
    (x : (fiberTriangle t ht).obj₁ ⟶ (shiftFunctor (hoFunctor.obj X) n).obj W) :
    fiberContravariantHomConnecting W t ht n x =
      (fiberTriangle t ht).mor₃ ≫ (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map x ≫
        (shiftFunctorAdd' (hoFunctor.obj X) n 1 (n + 1) rfl).inv.app W :=
  preadditiveYoneda_homologySequenceδ_apply (fiberTriangle t ht) n (n + 1) rfl x

/-- 概要：fiber 列の反変 Hom 長完全列の六項部分列。
方針：反対三角形に加法的 yoneda のホモロジー関手性を適用する。
規約：全整数 n で Hom(C,W[n]) から始まる。使われ方：S5 の反変 Hom 長完全列。 -/
def fiberContravariantHomSequence {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (fiberContravariantHomFunctor W).homologySequenceComposableArrows₅
    ((triangleOpEquivalence (hoFunctor.obj X)).functor.obj (op (fiberTriangle t ht))) n (n + 1) rfl

/-- 概要：fiber 列の反変 Hom 長完全列は全整数次数で完全。
方針：反対三角形の distinguished 性と加法的 yoneda のホモロジー関手性を使う。
規約：隣接次数をまたぐ位置を含む六項の完全性。使われ方：S5 の反変 Hom 長完全列。 -/
lemma fiberContravariantHomSequence_exact {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (W : hoFunctor.obj X) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (n : ℤ) :
    (fiberContravariantHomSequence W t ht n).Exact :=
  (fiberContravariantHomFunctor W).homologySequenceComposableArrows₅_exact _
    (op_distinguished _ (fiberTriangle_distinguished t ht)) n (n + 1) rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
