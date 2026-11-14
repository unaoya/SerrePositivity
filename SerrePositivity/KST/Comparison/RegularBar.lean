module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.GroupCompletion
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy

/-!
# 正則作用の分類圏と収縮

概要：モノイドの自身への正則作用の圏を作り、その nerve を実際に収縮する。
方針：射 a→b を m*a=b となる m とし、単位からの射の自然変換を使う。
規約：群や各元の逆元を要求しない。Segal 1974 Proposition 1.5 の全空間の模型。
使われ方：bar の universal bundle と群完備化の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.Comparison

open CategoryTheory

/--
概要：モノイドの正則左作用の分類圏の対象。
方針：元に専用の型タグを付けて既存の圏構造と区別する。
規約：群状性はまだ仮定しない。Segal 1974 Proposition 1.5 の全空間。
使われ方：作用の分類圏の合成と収縮。
-/
structure RegularAction (M : Type u) where
  /-- 概要：作用されるモノイドの元。方針：型タグの値。規約：正則作用。使われ方：射の条件。 -/
  val : M

variable (M : Type u) [Monoid M]

/--
概要：正則作用の射 a→b は m*a=b を満たすラベル m である。
方針：合成をラベルの通常順の積で定める。
規約：先の射 f、後の射 g の合成のラベルは g*f。
使われ方：Segal 1974 Proposition 1.5 の contractible な全空間の nerve。
-/
instance regularActionCategory : Category (RegularAction M) where
  Hom a b := {m : M // m * a.val = b.val}
  id a := ⟨1, one_mul a.val⟩
  comp f g := ⟨g.val * f.val, by rw [mul_assoc, f.property, g.property]⟩
  id_comp f := Subtype.ext (mul_one f.val)
  comp_id f := Subtype.ext (one_mul f.val)
  assoc f g h := Subtype.ext (mul_assoc h.val g.val f.val).symm

/--
概要：正則作用の分類圏から一対象圏へラベルを忘れずに射影する。
方針：全ての対象を唯一の対象へ送り、射をそのラベルへ送る。
規約：射の合成の順序は SingleObj と同じ。Segal 1974 Proposition 1.5。
使われ方：普遍 bar 束の分類空間への写像。
-/
def regularActionProjection : RegularAction M ⥤ SingleObj M where
  obj _ := SingleObj.star M
  map f := f.val

variable {M} {N : Type v} [Monoid N]

/--
概要：モノイド準同型は正則作用の圏の間の関手を誘導する。
方針：対象の元と射のラベルの両方に準同型を適用する。
規約：積の順序を変えない。Segal 1974 Proposition 1.5 の自然性。
使われ方：正則作用の二重単体的 bar。
-/
def regularActionMap (f : M →* N) : RegularAction M ⥤ RegularAction N where
  obj a := ⟨f a.val⟩
  map g := ⟨f g.val, by rw [← map_mul, g.property]⟩
  map_id a := Subtype.ext (map_one f)
  map_comp g h := Subtype.ext (map_mul f h.val g.val)

/--
概要：単位の対象から恒等関手への自然変換を構成する。
方針：各 a に対してラベル a の射 1→a を取り、自然性を射の条件から示す。
規約：逆元は不要。Segal 1974 Proposition 1.5 の全空間の収縮。
使われ方：nerve 上の実際の単体的ホモトピー。
-/
def regularActionContraction : (Functor.const (RegularAction M)).obj ⟨1⟩ ⟶ 𝟭 (RegularAction M) where
  app a := ⟨a.val, mul_one a.val⟩
  naturality {a b} f := by
    apply Subtype.ext
    change b.val * 1 = f.val * a.val
    rw [f.property, mul_one]

/--
概要：正則作用の圏の nerve の定数写像から恒等写像への実単体的ホモトピー。
方針：単位からの自然変換を既存の nerve のホモトピー構成に渡す。
規約：群状性を使わず任意のモノイドに成立する。Segal 1974 Proposition 1.5。
使われ方：universal bar の全空間の可縮性。
-/
noncomputable def regularActionNerveContraction :
    SSet.Homotopy (nerveMap ((Functor.const (RegularAction M)).obj ⟨1⟩))
      (nerveMap (𝟭 (RegularAction M))) :=
  NerveHomotopy.homotopy (regularActionContraction (M := M))

/--
概要：モノイドの正則作用の分類圏を関手としてまとめる。
方針：対象とラベルへの準同型の作用を使う。
規約：対象と射の宇宙は u。Segal 1974 Proposition 1.5 の普遍 bar。
使われ方：単体的モノイドの各次数での正則作用。
-/
def regularActionFunctor : MonCat.{u} ⥤ Cat.{u, u} where
  obj M := Cat.of (RegularAction M)
  map f := (regularActionMap f.hom).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/--
概要：単体的モノイドの正則作用の二重単体的 nerve。
方針：各次数で正則作用の分類圏の nerve を取り、準同型で結ぶ。
規約：Segal 1974 Proposition 1.5 の可縮な全空間の二重単体模型。
使われ方：普遍 bar 束の全空間。
-/
def bisimplicialRegularBar (M : SimplicialObject MonCat.{u}) : SimplicialObject SSet.{u} :=
  M ⋙ regularActionFunctor ⋙ nerveFunctor

/--
概要：単体的モノイドの正則 bar の全空間を対角で定義する。
方針：二重単体的正則 bar を二つの単体次数の対角に制限する。
規約：行ごとの収縮を対角の収縮へ移す段階は別途証明する。
使われ方：Segal 1974 Proposition 1.5 の普遍束と群完備化。
-/
def regularBar (M : SimplicialObject MonCat.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (bisimplicialRegularBar M)

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.2.2.4" (partial := special) "仮定：通常のモノイド M（Lean は HA の集合の圏の場合に限る）。結論：M の正則左作用の圏から基底の単一対象圏への射影を与える（M の自己作用の成分に一致）。[n]↦[n+1] の移送による一般の左作用図式の構成は含まれない。"] _root_.SerrePositivity.KST.Comparison.regularActionProjection
