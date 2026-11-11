module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.HomCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantObjectNaturality

/-!
概要：h Fun に表示した自然な Hom 対応から quasicategory の随伴を構成する。
方針：前後合成とパラメータ前合成の自然性を双圏の対応へ移す。
規約：任意の関手 U,V の二胞体を扱い、hX と hY の Hom だけに弱めない。
使われ方：写像空間の自然な対応から単位・余単位へ進む代数的な接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：関手単体集合のホモトピー圏の二胞体。
方針：二つの関手頂点の間の射を使う。
規約：標的の quasicategory 性は不要。
使われ方：自然なパラメータ付き Hom 対応の簡潔な表示。 -/
abbrev FunctorHom {A X : SSet.{u}} (U V : A ⟶ X) :=
  (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) : hoFunctor.obj ((ihom A).obj X)) ⟶
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)

/-- 概要：h Fun の二変数とパラメータに自然な Hom 全単射。
方針：任意の U,V の全単射と前後合成・パラメータ前合成の整合を記録する。
規約：単位・余単位と三角恒等式は入力に含まない。
使われ方：quasicategory の双圏随伴を構成する中間表示。 -/
@[ext] structure QCatFunctorHomCorrespondence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (G : Y ⟶ X) where
  equiv : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
    FunctorHom (U ≫ F) V ≃ FunctorHom U (V ≫ G)
  naturality_right : ∀ {A : SSet.{u}} [Quasicategory A]
    {U : A ⟶ X} {V V' : A ⟶ Y} (α : FunctorHom (U ≫ F) V) (β : FunctorHom V V'),
    equiv U V' (α ≫ β) = equiv U V α ≫ (hoFunctor.map ((ihom A).map G)).toFunctor.map β
  naturality_left : ∀ {A : SSet.{u}} [Quasicategory A]
    {U U' : A ⟶ X} {V : A ⟶ Y} (γ : FunctorHom U' U) (α : FunctorHom (U ≫ F) V),
    equiv U' V ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) = γ ≫ equiv U V α
  precomp : ∀ {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (i : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y) (α : FunctorHom (U ≫ F) V),
    equiv (i ≫ U) (i ≫ V) ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) =
      (hoFunctor.map ((pre i).app X)).toFunctor.map (equiv U V α)

local instance correspondenceHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B
local instance correspondenceObjectQuasicategory (A : SSet.QCat.{u}) : Quasicategory A.obj :=
  A.property

namespace QCatFunctorHomCorrespondence
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

/-- 概要：h Fun の自然な対応を QCat 双圏の対応へ移す。
方針：二胞体の表示同値と前後の whisker の比較を使う。
規約：同じ底の関手を保つ。
使われ方：双圏で証明した三角恒等式の適用。 -/
def toBicategory (e : QCatFunctorHomCorrespondence F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) where
  equiv U V := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U.hom ≫ F) V.hom).trans
    ((e.equiv U.hom V.hom).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U.hom (V.hom ≫ G)).symm)
  naturality_right {A} {U} {V V'} α β := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U.hom (V'.hom ≫ G)).injective
    change e.equiv U.hom V'.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ β) =
      e.equiv U.hom V.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (V.hom ≫ G) (V'.hom ≫ G) (β ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)
    exact (e.naturality_right _ _).trans
      (congrArg (e.equiv U.hom V.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) ≫ ·)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := V.hom) (V := V'.hom) β G).symm)
  naturality_left {A} {U U'} {V} γ α := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U'.hom (V.hom ≫ G)).injective
    change e.equiv U'.hom V.hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U'.hom ≫ F) (U.hom ≫ F) (γ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ γ ≫ e.equiv U.hom V.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α)
    have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U'.hom ≫ F) (U.hom ≫ F) (γ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) =
        (hoFunctor.map ((ihom A.obj).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ γ) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := U'.hom) (V := U.hom) γ F
    exact (congrArg (fun t ↦ e.equiv U'.hom V.hom (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α)) hw).trans
      (e.naturality_left _ _)
  precomp {A B} i {U V} α := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (i.hom ≫ U.hom) ((i.hom ≫ V.hom) ≫ G)).injective
    simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    change e.equiv (i.hom ≫ U.hom) (i.hom ≫ V.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (i ◁ α)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (i ◁
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U.hom (V.hom ≫ G)).symm
          (e.equiv U.hom V.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α))))
    have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft i.hom (F := U.hom ≫ F) (G := V.hom) α
    have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft i.hom
      (F := U.hom) (G := V.hom ≫ G)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U.hom (V.hom ≫ G)).symm
        (e.equiv U.hom V.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α)))
    exact (congrArg (e.equiv (i.hom ≫ U.hom) (i.hom ≫ V.hom)) h₁).trans
      ((e.precomp i.hom U.hom V.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α)).trans h₂.symm)

/-- 概要：h Fun の自然な Hom 対応から随伴を構成する。
方針：双圏の対応に移し、単位・余単位と三角恒等式の構成を適用する。
規約：随伴の存在を入力として要求しない。
使われ方：写像空間の特徴づけの逆方向の代数的な段階。 -/
def toAdjunction (e : QCatFunctorHomCorrespondence F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  e.toBicategory.toAdjunction

/-- 概要：随伴から h Fun の自然な Hom 対応を取り出す。
方針：既存の一般の adjunct 全単射と前後合成・前合成自然性を使う。
規約：定値関手に制限しない。
使われ方：Hom 対応による特徴づけの順方向。 -/
def ofAdjunction (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) : QCatFunctorHomCorrespondence F G where
  equiv := a.homEquiv
  naturality_right := fun {_} _ {_} {_ _} α β ↦ a.homEquiv_comp_right _ _ _ α β
  naturality_left := fun {_} _ {_ _} {_} γ α ↦ a.homEquiv_comp_left _ _ _ γ α
  precomp := a.homEquiv_precomp

/-- 概要：構成した随伴の h Fun の adjunct は元の対応と一致する。
方針：双圏での回収の定理を二胞体の表示同値で移す。
規約：U,V は定値関手に限らない。
使われ方：対応から随伴への構成の往復。 -/
lemma toAdjunction_homEquiv (e : QCatFunctorHomCorrespondence F G)
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y) :
    e.toAdjunction.homEquiv U V = e.equiv U V := by
  apply Equiv.ext
  intro α
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U (V ≫ G)
    (e.toBicategory.toAdjunction.homEquiv₂ (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U) (h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ F) V).symm α)) = _
  rw [e.toBicategory.toAdjunction_homEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V)]
  rfl

/-- 概要：随伴からの h Fun の対応は双圏の標準対応に移る。
方針：二胞体の表示同値の両逆を計算する。
規約：全てのパラメータを含む構造体の等式。
使われ方：随伴の回収。 -/
lemma toBicategory_ofAdjunction (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) :
    (ofAdjunction a).toBicategory = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence.ofAdjunction a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence.ext
  funext A U V
  apply Equiv.ext
  intro α
  rfl

/-- 概要：随伴から h Fun の対応を経由して戻すと元の随伴。
方針：双圏の対応との一致と、そこでの回収の定理を使う。
規約：単位・余単位を含めて一致する。
使われ方：h Fun の Hom 対応による随伴の特徴づけ。 -/
lemma ofAdjunction_toAdjunction (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) :
    (ofAdjunction a).toAdjunction = a := by
  change (ofAdjunction a).toBicategory.toAdjunction = a
  rw [toBicategory_ofAdjunction, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence.ofAdjunction_toAdjunction]

/-- 概要：h Fun の自然な Hom 対応と quasicategory の随伴の全単射。
方針：自然性からの単位・余単位の構成と両方向の回収を使う。
規約：写像空間そのものの対応からこの型を構成する橋は別段階。
使われ方：写像空間による特徴づけの逆方向の代数的な終点。 -/
def adjunctionEquiv : QCatFunctorHomCorrespondence F G ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G where
  toFun := toAdjunction
  invFun := ofAdjunction
  left_inv e := by
    apply QCatFunctorHomCorrespondence.ext
    funext A _ U V
    exact e.toAdjunction_homEquiv U V
  right_inv := ofAdjunction_toAdjunction

/-- 概要：構成した随伴の単位は恒等関手の左単位子の像。
方針：双圏の単位の構成と二胞体の表示を展開する。
規約：対象ごとの成分に忘却せず h Fun(X,X) の射として述べる。
使われ方：写像空間対応から得る単位の仕様。 -/
lemma toAdjunction_unitHom (e : QCatFunctorHomCorrespondence F G) :
    e.toAdjunction.unitHom = e.equiv (𝟙 X) F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv ((𝟙 X) ≫ F) F (Bicategory.leftUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)).hom) := rfl

/-- 概要：構成した随伴の余単位は右随伴の左単位子の逆像。
方針：双圏の余単位の構成と二胞体の表示を展開する。
規約：h Fun(Y,Y) の射として述べる。
使われ方：写像空間対応から得る余単位の仕様。 -/
lemma toAdjunction_counitHom (e : QCatFunctorHomCorrespondence F G) :
    e.toAdjunction.counitHom = (e.equiv G (𝟙 Y)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv G ((𝟙 Y) ≫ G) (Bicategory.leftUnitor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).inv) := rfl

end QCatFunctorHomCorrespondence
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
