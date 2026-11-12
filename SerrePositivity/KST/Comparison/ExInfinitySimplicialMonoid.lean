module

public import SerrePositivity.KST.Comparison.SimplicialMonoidInternal
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityMonoidal

/-!
# 単体的モノイドの Ex∞ 置換

概要：既存の単体的モノイドの入力に Ex∞ のモノイド置換を適用する。
方針：内部モノイドへ移し、monoidal な Ex∞ を適用してから戻す。
規約：KST Lemma 2.13 の bar の入力の型は変更しない。
使われ方：Kan な基礎単体集合を持つ単体的モノイドへの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite

/--
概要：単体的モノイドを内部モノイドへ移して戻す際の、恒等な基礎写像を持つ比較。
方針：各次数で恒等写像を単位と積を保つモノイド射として束ねる。
規約：基礎単体集合上で恒等であることを保つ移送。
使われ方：元の単体的モノイドから置換への自然な射。
-/
def simplicialMonoidInternalUnit : 𝟭 (SimplicialObject MonCat.{u}) ⟶
    simplicialMonoidToInternal ⋙ internalMonoidToSimplicial where
  app _M :=
    { app _d := MonCat.ofHom
        { toFun := fun x => x
          map_one' := rfl
          map_mul' _ _ := rfl }
      naturality _ _ _ := rfl }
  naturality _ _ _ := rfl

/--
概要：基礎単体集合が Kan となる単体的モノイドの Ex∞ 置換関手。
方針：内部モノイドの Ex∞ 置換を既存の単体的モノイドへ戻す。
規約：bar の構成は従来の SimplicialObject MonCat の界面を使う。
使われ方：群状モノイドの bar の Kan 模型。
-/
def exInfinitySimplicialMonoidFunctor : SimplicialObject MonCat.{u} ⥤ SimplicialObject MonCat.{u} :=
  simplicialMonoidToInternal ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidFunctor ⋙ internalMonoidToSimplicial

/--
概要：単体的モノイドから Ex∞ による置換への自然なモノイド射。
方針：内部モノイドへの往復の比較と Ex∞ のモノイドの単位を合成する。
規約：この射の基礎写像は Ex∞ の単位に一致する。
使われ方：元の bar と Kan 模型の比較写像。
-/
def exInfinitySimplicialMonoidUnit : 𝟭 (SimplicialObject MonCat.{u}) ⟶
    exInfinitySimplicialMonoidFunctor :=
  simplicialMonoidInternalUnit ≫ Functor.whiskerLeft simplicialMonoidToInternal
    (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit internalMonoidToSimplicial)

/--
概要：置換した単体的モノイドの基礎単体集合は元の基礎単体集合の Ex∞ である。
方針：内部モノイドへの往復の基礎対象の定義を使う。
規約：積・単位の移送と基礎対象の Kan 性を分けて扱う。
使われ方：bar の各行を Kan 複体の積として扱う。
-/
theorem exInfinitySimplicialMonoid_space (M : SimplicialObject MonCat.{u}) :
    monoidSpace (exInfinitySimplicialMonoidFunctor.obj M) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (monoidSpace M) := rfl

/--
概要：置換した単体的モノイドの基礎単体集合は Kan 複体である。
方針：基礎単体集合を実際の Ex∞ と同定する。
規約：元のモノイドの Kan 性は仮定しない。
使われ方：bar の行の射影を Kan な対象の上で扱う。
-/
instance exInfinitySimplicialMonoid_kanComplex (M : SimplicialObject MonCat.{u}) :
    SSet.KanComplex (monoidSpace (exInfinitySimplicialMonoidFunctor.obj M)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex (monoidSpace M)

/--
概要：単体的モノイドの置換への射の基礎写像は Ex∞ の単位である。
方針：往復の比較の基礎写像が恒等で、内部モノイドの単位が Ex∞ の単位であることを使う。
規約：既存の忘却関手によって基礎単体集合の射を表す。
使われ方：単体的モノイドの bar の比較の局所化での可逆性。
-/
theorem exInfinitySimplicialMonoidUnit_space (M : SimplicialObject MonCat.{u}) :
    Functor.whiskerRight (exInfinitySimplicialMonoidUnit.app M) (forget MonCat) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (monoidSpace M) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/--
概要：単体的モノイドの置換への射は、基礎単体集合の anodyne 局所化で可逆である。
方針：基礎写像を Ex∞ の単位に同定する。
規約：bar 比較の弱同値の入力。
使われ方：元の単体的モノイドから Kan な模型への移行。
-/
instance exInfinitySimplicialMonoidUnit_localized_isIso (M : SimplicialObject MonCat.{u}) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (Functor.whiskerRight (exInfinitySimplicialMonoidUnit.app M) (forget MonCat))) := by
  rw [exInfinitySimplicialMonoidUnit_space]
  infer_instance

end SerrePositivity.KST.Comparison
