module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：関手単体集合のホモトピー圏の可逆な二胞体による quasicategory の同値。
方針：閉構造で射を頂点にし、前後合成と評価をホモトピー圏へ移す。
規約：逆データの条件は hX の圏同値より強く、h Fun(X,X) の同型である。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY）、Construction 4.5.1.23（Tag 02BZ）、HTT §1.2.10。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：単体集合の射に対応する関手単体集合の頂点。
方針：閉構造の curry' と単位からの射の零単体表示を合成する。
規約：quasicategory 性は不要。
使われ方：Kerodon Construction 4.5.1.23（Tag 02BZ） の一胞体。 -/
@[kerodon 00TS, kerodon 00TX]
def functorVertex {X Y : SSet.{u}} (f : X ⟶ Y) : ((ihom X).obj Y) _⦋0⦌ :=
  SSet.unitHomEquiv _ (curry' f)

/-- 概要：平行な単体集合の射の間の可逆な二胞体。
方針：関手単体集合のホモトピー圏の同型を使う。
規約：単なる頂点ごとの同型の族ではない。
使われ方：Kerodon Construction 4.5.1.23（Tag 02BZ） の可逆な二胞体。 -/
abbrev FunctorIso {X Y : SSet.{u}} (f g : X ⟶ Y) :=
  (SSet.HomotopyCategory.mk (functorVertex f) : hoFunctor.obj ((ihom X).obj Y)) ≅
    SSet.HomotopyCategory.mk (functorVertex g)

/-- 概要：単体集合の二頂点の同型。
方針：ホモトピー圏の対象としての同型を使う。
規約：頂点そのものの等式を要求しない。
使われ方：HTT §1.2.4、Kerodon §4.4（Tag 01EM） の対象の同値。 -/
abbrev VertexIso {X : SSet.{u}} (x y : X _⦋0⦌) :=
  (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk y

/-- 概要：頂点の同型は任意の単体集合の射で写せる。
方針：ホモトピー圏の関手で同型を写す。
規約：射の可逆性は不要。
使われ方：HTT §1.2.4 の同型の関手性。 -/
def VertexIso.map {X Y : SSet.{u}} {x y : X _⦋0⦌} (e : VertexIso x y) (f : X ⟶ Y) :
    VertexIso (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) :=
  (hoFunctor.map f).toFunctor.mapIso e

/-- 概要：quasicategory の同値の明示的な逆データ。
方針：逆射と、二つの合成から恒等への可逆二胞体を保持する。
規約：合成 f≫g の順序はまず f、次に g。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY）、Construction 4.5.1.23（Tag 02BZ）。 -/
@[kerodon 01DY]
structure QCatEquivalence (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] where
  /-- 順方向の単体集合の射。 -/
  hom : X ⟶ Y
  /-- 逆方向の単体集合の射。 -/
  inv : Y ⟶ X
  /-- X 上の合成から恒等への可逆二胞体。 -/
  homInvIso : FunctorIso (hom ≫ inv) (𝟙 X)
  /-- Y 上の合成から恒等への可逆二胞体。 -/
  invHomIso : FunctorIso (inv ≫ hom) (𝟙 Y)

/-- 概要：指定された射が quasicategory の同値であるという性質。
方針：逆射と二つの可逆二胞体の存在で定義する。
規約：射 f を固定し、選択された逆射を命題には含めない。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY）、充満忠実性による同値の判定。 -/
@[kerodon 01DY]
def IsQCatEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Nonempty (FunctorIso (f ≫ g) (𝟙 X)) ∧
    Nonempty (FunctorIso (g ≫ f) (𝟙 Y))

/-- 概要：選択された同値の順方向の射は同値という性質を持つ。
方針：構造中の逆射と二胞体を存在量化する。
規約：追加の選択は不要。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY） のデータと性質の接続。 -/
lemma QCatEquivalence.isQCatEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : IsQCatEquivalence e.hom :=
  ⟨e.inv, ⟨e.homInvIso⟩, ⟨e.invHomIso⟩⟩

/-- 概要：同値という性質から明示的な同値の逆データを選ぶ。
方針：存在する逆射と非空な二胞体の型から元を選ぶ。
規約：順方向の射は指定された f のまま。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY） の利用側 API。 -/
noncomputable def IsQCatEquivalence.choose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (h : IsQCatEquivalence f) : QCatEquivalence X Y where
  hom := f
  inv := Exists.choose h
  homInvIso := (Exists.choose_spec h).1.some
  invHomIso := (Exists.choose_spec h).2.some

/-- 概要：可逆二胞体を標的の射で後合成する。
方針：内部 Hom の共変な関手性をホモトピー圏へ移す。
規約：q 自体の可逆性は不要。
使われ方：Kerodon Proposition 4.5.1.5（Tag 01DU）、同値の合成。 -/
def FunctorIso.postcomp {X Y Z : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) (q : Y ⟶ Z) :
    FunctorIso (f ≫ q) (g ≫ q) := by
  have hf : ((ihom X).map q).app (Opposite.op ⦋0⦌) (functorVertex f) =
      functorVertex (f ≫ q) := rfl
  have hg : ((ihom X).map q).app (Opposite.op ⦋0⦌) (functorVertex g) =
      functorVertex (g ≫ q) := rfl
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hf)).symm ≪≫
    (hoFunctor.map ((ihom X).map q)).toFunctor.mapIso e ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hg)

/-- 概要：可逆二胞体を始域の射で前合成する。
方針：内部 Hom の反変な前合成をホモトピー圏へ移す。
規約：q 自体の可逆性は不要。
使われ方：Kerodon Proposition 4.5.1.5（Tag 01DU）、同値の合成。 -/
def FunctorIso.precomp {W X Y : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) (q : W ⟶ X) :
    FunctorIso (q ≫ f) (q ≫ g) := by
  have hf : ((pre q).app Y).app (Opposite.op ⦋0⦌) (functorVertex f) =
      functorVertex (q ≫ f) := by
    rfl
  have hg : ((pre q).app Y).app (Opposite.op ⦋0⦌) (functorVertex g) =
      functorVertex (q ≫ g) := by
    rfl
  have h := VertexIso.map e ((pre q).app Y)
  rw [hf, hg] at h
  exact h

/-- 概要：恒等射は quasicategory の同値。
方針：両方の合成が恒等射である等式を同型にする。
規約：任意の quasicategory。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY） の単位。 -/
def QCatEquivalence.refl (X : SSet.{u}) [Quasicategory X] : QCatEquivalence X X where
  hom := 𝟙 X
  inv := 𝟙 X
  homInvIso := eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
    (Category.id_comp (𝟙 X)))
  invHomIso := eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
    (Category.id_comp (𝟙 X)))

/-- 概要：quasicategory の同値を逆にする。
方針：射と逆射、二つの二胞体を交換する。
規約：追加の選択や充填は不要。
使われ方：Kerodon Definition 4.5.1.10（Tag 01DY） の対称性。 -/
def QCatEquivalence.symm {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : QCatEquivalence Y X where
  hom := e.inv
  inv := e.hom
  homInvIso := e.invHomIso
  invHomIso := e.homInvIso

/-- 概要：quasicategory の同値を合成する。
方針：二胞体の前後合成で中間の逆合成を消し、残る逆合成も消す。
規約：逆射は逆順に合成する。
使われ方：Kerodon Proposition 4.5.1.5（Tag 01DU） の合成則。 -/
def QCatEquivalence.trans {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory Z] (e : QCatEquivalence X Y) (d : QCatEquivalence Y Z) :
    QCatEquivalence X Z where
  hom := e.hom ≫ d.hom
  inv := d.inv ≫ e.inv
  homInvIso := by
    have h := (FunctorIso.postcomp (FunctorIso.precomp d.homInvIso e.hom) e.inv) ≪≫ e.homInvIso
    simpa only [Category.assoc, Category.comp_id] using h
  invHomIso := by
    have h := (FunctorIso.postcomp (FunctorIso.precomp e.invHomIso d.inv) d.hom) ≪≫ d.invHomIso
    simpa only [Category.assoc, Category.comp_id] using h

/-- 概要：関手単体集合のホモトピー圏からホモトピー圏間の関手の圏への評価。
方針：h の積比較の逆関手と単体的評価を合成し、通常の関手を curry する。
規約：対象も始域も任意の単体集合でよい。
使われ方：Kerodon Proposition 4.5.1.5（Tag 01DU） の二胞体の通常の自然変換への移送。 -/
def functorHomotopyEvaluation (X Y : SSet.{u}) :
    hoFunctor.obj ((ihom X).obj Y) ⥤ (hoFunctor.obj X ⥤ hoFunctor.obj Y) :=
  Functor.curry.obj
    (SSet.Truncated.HomotopyCategory.BinaryProduct.inverse
      ((truncation 2).obj ((ihom X).obj Y)) ((truncation 2).obj X) ⋙
      (hoFunctor.map ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y)).toFunctor)

/-- 概要：関手単体集合の頂点の評価は元の射のホモトピー圏への作用。
方針：頂点と辺の生成元上で評価の定義を計算する。
規約：h の対象を零単体の表示で比較する。
使われ方：Kerodon Proposition 4.5.1.5（Tag 01DU） の同値を通常の圏同値へ送る手順。 -/
lemma functorHomotopyEvaluation_obj {X Y : SSet.{u}} (f : X ⟶ Y) :
    (functorHomotopyEvaluation X Y).obj (SSet.HomotopyCategory.mk (functorVertex f)) =
      (hoFunctor.map f).toFunctor := by
  refine SSet.Truncated.HomotopyCategory.functor_ext (fun _ ↦ rfl) ?_
  intro x y e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：可逆二胞体はホモトピー圏間の自然同型を誘導する。
方針：評価関手で同型を写し、射の評価の計算で両端を同定する。
規約：可逆性は関手単体集合のホモトピー圏で仮定する。
使われ方：Kerodon Proposition 4.5.1.5（Tag 01DU）、同値のホモトピー圏への移送。 -/
def FunctorIso.toNatIso {X Y : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) :
    (hoFunctor.map f).toFunctor ≅ (hoFunctor.map g).toFunctor :=
  (eqToIso (functorHomotopyEvaluation_obj f)).symm ≪≫
    (functorHomotopyEvaluation X Y).mapIso e ≪≫ eqToIso (functorHomotopyEvaluation_obj g)

/-- 概要：quasicategory の同値はホモトピー圏の通常の圏同値を誘導する。
方針：二胞体の評価による自然同型を単位と余単位にし、三角恒等式を整える。
規約：順方向の関手は正確に hoFunctor.map e.hom。
使われ方：HTT §1.2.10、Kerodon Proposition 4.5.1.5（Tag 01DU） の同値の不変量。 -/
def QCatEquivalence.toHoEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : hoFunctor.obj X ≌ hoFunctor.obj Y :=
  CategoryTheory.Equivalence.mk (hoFunctor.map e.hom).toFunctor (hoFunctor.map e.inv).toFunctor
    (by simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Cat.Hom.comp_toFunctor,
      Cat.Hom.id_toFunctor] using (FunctorIso.toNatIso e.homInvIso).symm)
    (by simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Cat.Hom.comp_toFunctor,
      Cat.Hom.id_toFunctor] using FunctorIso.toNatIso e.invHomIso)

/-- 概要：誘導されたホモトピー圏の同値の順方向は指定された射の像。
方針：通常の同値構成の定義を計算する。
規約：自然同型による同定に留めず関手の等号を与える。
使われ方：HTT §1.2.10 の同値の関手性。 -/
lemma QCatEquivalence.toHoEquivalence_functor {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.toHoEquivalence.functor = (hoFunctor.map e.hom).toFunctor := rfl

/-- 概要：誘導されたホモトピー圏の同値の逆方向は逆射の像。
方針：通常の同値構成の定義を計算する。
規約：三角恒等式を整えても逆関手自体は変わらない。
使われ方：HTT §1.2.10 の同値の逆。 -/
lemma QCatEquivalence.toHoEquivalence_inverse {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.toHoEquivalence.inverse = (hoFunctor.map e.inv).toFunctor := rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
