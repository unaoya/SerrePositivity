module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の単位・余単位による随伴。
方針：Mathlib の `SSet.QCat.strictBicategory` の双圏随伴を使う。
規約：二胞体は h Fun の射であり、hX と hY の随伴で代用しない。
使われ方：Kerodon Def 6.1.1.1（Tag 02CG）、Def 6.2.1.1（Tag 02EK）、Remark 6.2.1.4（Tag 02EN）、HTT §5.2。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：単体集合として与えた quasicategory を双圏の対象とする。
方針：充満部分圏の対象を作る。規約：宇宙は変えない。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN） のホモトピー双圏。 -/
abbrev qcatOf (X : SSet.{u}) [Quasicategory X] : SSet.QCat.{u} := ⟨X, inferInstance⟩

/-- 概要：単体集合の射を双圏の一胞体にする。
方針：充満部分圏の射を使う。規約：底の射を変えない。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN）。 -/
abbrev qcatMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) :
    qcatOf X ⟶ qcatOf Y := ObjectProperty.homMk F

/-- 概要：quasicategory の関手の随伴。
方針：単位・余単位と h Fun 内の三角恒等式を持つ双圏随伴を使う。
規約：単位・余単位を可逆とは仮定しない。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK）・Remark 6.2.1.4（Tag 02EN）、HTT §5.2。 -/
@[kerodon 02EK, kerodon 02EL, kerodon 02EN]
abbrev QCatAdjunction {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (F : X ⟶ Y) (G : Y ⟶ X) := Bicategory.Adjunction (qcatMap F) (qcatMap G)

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：双圏の Hom 圏から関手単体集合のホモトピー圏への表示。
方針：Cat への豊穣構造の底の二胞体を取る。規約：対象は既存の functorVertex。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN）、A3a の FunctorIso との接続。 -/
@[kerodon 02EN]
def qcatHomFunctor (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] :
    (qcatOf X ⟶ qcatOf Y) ⥤ hoFunctor.obj ((ihom X).obj Y) where
  obj F := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)
  map α := CatEnrichedOrdinary.Hom.base α

/-- 概要：Hom 圏の表示は二胞体の等式を反映する。
方針：豊穣二胞体の外側の包みは底の射で決まる。
規約：対象の同一視ではなく、各 Hom 上の忠実性。
使われ方：h Fun の三角恒等式から随伴を構成する。 -/
instance qcatHomFunctor_faithful (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] :
    (qcatHomFunctor X Y).Faithful where
  map_injective h := CatEnrichedOrdinary.Hom.ext _ _ h

/-- 概要：h Fun の射と双圏の二胞体は同じデータ。
方針：豊穣 Hom の包みを外す。規約：ホモトピー圏間の自然変換への忘却ではない。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN） の二胞体の同定。 -/
@[kerodon 02EN]
def qcatCellEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F G : X ⟶ Y) :
    (qcatMap F ⟶ qcatMap G) ≃
      ((SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : hoFunctor.obj ((ihom X).obj Y)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) where
  toFun α := CatEnrichedOrdinary.Hom.base α
  invFun α := CatEnrichedOrdinary.Hom.mk α
  left_inv _ := rfl
  right_inv _ := rfl

/-- 概要：単体的ホモトピーを関手単体集合の辺として表す。
方針：curry した区間の射の一次単体を取り、両端を計算する。
規約：区間の向きは A1c と同じ 0 から 1。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN）、単位・余単位の代表。 -/
noncomputable def functorEdgeOfHomotopy {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.ι₀ ≫ H)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.ι₁ ≫ H)) where
  edge := SSet.yonedaEquiv (curry H)
  src_eq := by
    change ((ihom X).obj Y).map (SimplexCategory.δ (1 : Fin 2)).op
      (SSet.yonedaEquiv (curry H)) = _
    simpa only [Equiv.symm_apply_apply, uncurry_curry, SimplicialObject.δ] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero (SSet.yonedaEquiv (curry H))).symm
  tgt_eq := by
    change ((ihom X).obj Y).map (SimplexCategory.δ (0 : Fin 2)).op
      (SSet.yonedaEquiv (curry H)) = _
    simpa only [Equiv.symm_apply_apply, uncurry_curry, SimplicialObject.δ] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_one (SSet.yonedaEquiv (curry H))).symm

/-- 概要：単体的ホモトピーの類を双圏の二胞体にする。
方針：curry した辺の homMk を h Fun の表示同値で戻す。
規約：可逆性を仮定しない。始域・標的は quasicategory。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK）、A1c のホモトピーの二胞体表示。 -/
noncomputable def qcatCellOfHomotopy {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (H : X ⊗ Δ[1] ⟶ Y) : qcatMap (SSet.ι₀ ≫ H) ⟶ qcatMap (SSet.ι₁ ≫ H) :=
  (qcatCellEquiv _ _).symm (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfHomotopy H))

/-- 概要：h Fun の二胞体をホモトピー圏間の自然変換へ送る。
方針：A3a の評価関手で写し、対象の表示を両端で揃える。
規約：二胞体の可逆性は仮定しない。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN）、Cor 6.2.1.15（Tag 02EZ） の評価。 -/
def functorCellToNatTrans {X Y : SSet.{u}} {F G : X ⟶ Y}
    (α : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : hoFunctor.obj ((ihom X).obj Y)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    (hoFunctor.map F).toFunctor ⟶ (hoFunctor.map G).toFunctor :=
  eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj F).symm ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation X Y).map α ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj G)

/-- 概要：ホモトピーを h Fun の二胞体として評価すると A1c の自然変換になる。
方針：両辺を頂点で比較し、curry の評価と区間の恒等一次単体を計算する。
規約：quasicategory 性は不要。区間の向きも A1c と一致する。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN）、A1c と随伴の単位・余単位の接続。 -/
lemma functorCellToNatTrans_homotopy {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) :
    functorCellToNatTrans
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfHomotopy H)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans H := by
  unfold functorCellToNatTrans
  ext x
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  change SSet.Truncated.HomotopyCategory.homMk
      (((functorEdgeOfHomotopy H).tensor (SSet.Truncated.Edge.id x)).map
        ((truncation 2).map ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y))) =
    SSet.Truncated.HomotopyCategory.homMk
      (((SSet.Truncated.Edge.id x).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map H))
  congr 1
  apply SSet.Truncated.Edge.ext
  change ((ihom.ev X).app Y).app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id x).edge, SSet.yonedaEquiv (curry H)) =
    H.app (Opposite.op ⦋1⦌) ((SSet.Truncated.Edge.id x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  have h := congrArg
    (fun k : X ⊗ Δ[1] ⟶ Y => k.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) (uncurry_curry H)
  rw [uncurry_eq] at h
  change ((ihom.ev X).app Y).app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id x).edge, (curry H).app _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at h
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hc : (curry H).app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge =
      SSet.yonedaEquiv (curry H) := by
    rw [← hi, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rw [hc] at h
  exact h

/-- 概要：二胞体の評価は恒等射を保つ。
方針：評価関手の恒等射保存と両端の輸送の相殺。
規約：F は任意の単体集合の射。
使われ方：Kerodon Cor 6.2.1.15（Tag 02EZ） の準備。 -/
@[simp] lemma functorCellToNatTrans_id {X Y : SSet.{u}} (F : X ⟶ Y) :
    functorCellToNatTrans (𝟙 (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) =
      𝟙 (hoFunctor.map F).toFunctor := by
  simp [functorCellToNatTrans]

/-- 概要：二胞体の評価は縦合成を保つ。
方針：評価関手の合成保存と中間の輸送の相殺。
規約：二胞体は h Fun の射。
使われ方：Kerodon Cor 6.2.1.15（Tag 02EZ） の準備。 -/
@[simp] lemma functorCellToNatTrans_comp {X Y : SSet.{u}} {F G H : X ⟶ Y}
    (α : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : hoFunctor.obj ((ihom X).obj Y)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (β : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) : hoFunctor.obj ((ihom X).obj Y)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) :
    functorCellToNatTrans (α ≫ β) = functorCellToNatTrans α ≫ functorCellToNatTrans β := by
  simp [functorCellToNatTrans]

/-- 概要：ホモトピーから得た双圏の二胞体の評価は A1c と一致する。
方針：二胞体の包みを外し、h Fun の評価比較を適用する。
規約：quasicategory 性は二胞体を定義するためだけに必要。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN）、単位・余単位の通常の自然変換への表示。 -/
lemma qcatCellOfHomotopy_toNatTrans {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (H : X ⊗ Δ[1] ⟶ Y) :
    functorCellToNatTrans (qcatCellEquiv _ _ (qcatCellOfHomotopy H)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans H :=
  functorCellToNatTrans_homotopy H

/-- 概要：双圏の可逆二胞体を既存の FunctorIso にする。
方針：Hom 圏の表示関手で同型を写す。規約：底の関手は変えない。
使われ方：Kerodon §6.1.3（Tag 02D4）、A3a の同型 API。 -/
def qcatIsoToFunctorIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F G : X ⟶ Y} (e : qcatMap F ≅ qcatMap G) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  (qcatHomFunctor X Y).mapIso e

namespace QCatAdjunction

/-- 概要：h Fun に表示した三角恒等式から随伴を組み立てる。
方針：二つの表示関手の忠実性により双圏の三角恒等式に戻す。
規約：単位・余単位の入力は二胞体で、三角条件だけを h Fun の等式で受け取る。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK） と Remark 6.2.1.4 の定義の同値。 -/
@[kerodon 02EK]
def mkOfHomTriangles {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X}
    (η : 𝟙 (qcatOf X) ⟶ qcatMap F ≫ qcatMap G)
    (ε : qcatMap G ≫ qcatMap F ⟶ 𝟙 (qcatOf Y))
    (h₁ : (qcatHomFunctor X Y).map (Bicategory.leftZigzag η ε) =
      (qcatHomFunctor X Y).map
        ((Bicategory.leftUnitor (qcatMap F)).hom ≫ (Bicategory.rightUnitor (qcatMap F)).inv))
    (h₂ : (qcatHomFunctor Y X).map (Bicategory.rightZigzag η ε) =
      (qcatHomFunctor Y X).map
        ((Bicategory.rightUnitor (qcatMap G)).hom ≫ (Bicategory.leftUnitor (qcatMap G)).inv)) :
    QCatAdjunction F G where
  unit := η
  counit := ε
  left_triangle := (qcatHomFunctor X Y).map_injective h₁
  right_triangle := (qcatHomFunctor Y X).map_injective h₂


/-- 概要：恒等関手の自己随伴。
方針：双圏の恒等随伴。規約：指定された同じ対象を使う。
使われ方：Kerodon §6.1.1（Tag 02CF）。 -/
def refl (X : SSet.{u}) [Quasicategory X] : QCatAdjunction (𝟙 X) (𝟙 X) :=
  Bicategory.Adjunction.id (qcatOf X)

/-- 概要：随伴の合成。
方針：双圏の合成定理を使う。規約：右随伴の順序は逆。
使われ方：Kerodon Cor 6.1.5.5（Tag 02DT）、Remark 6.2.1.8（Tag 02ES）。 -/
@[kerodon 02ES]
def comp {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} {F' : Y ⟶ Z} {G' : Z ⟶ Y}
    (a : QCatAdjunction F G) (b : QCatAdjunction F' G') :
    QCatAdjunction (F ≫ F') (G' ≫ G) := Bicategory.Adjunction.comp a b

/-- 概要：同じ左随伴の右随伴は h Fun で同型。
方針：恒等二胞体の mate を取る。規約：関手そのものの等式は主張しない。
使われ方：Kerodon §6.1.3（Tag 02D4）、Remark 6.2.1.4（Tag 02EN）。 -/
def rightAdjointIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G G' : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F G') :
    qcatMap G ≅ qcatMap G' := Bicategory.conjugateIsoEquiv a b (Iso.refl _)

/-- 概要：同じ右随伴の左随伴は h Fun で同型。
方針：右側の恒等同型の逆 mate を取る。規約：一意性は二胞体の同型。
使われ方：Kerodon §6.1.3（Tag 02D4）、Remark 6.2.1.4（Tag 02EN）。 -/
def leftAdjointIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F' G) :
    qcatMap F ≅ qcatMap F' := ((Bicategory.conjugateIsoEquiv a b).symm (Iso.refl _)).symm

/-- 概要：随伴の単位を h Fun(X,X) で取り出す。
方針：二胞体の表示同値を使う。規約：対象ごとの単位だけに忘却しない。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK）。 -/
@[kerodon 02EL]
def unitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 X)) : hoFunctor.obj ((ihom X).obj X)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ G)) :=
  qcatCellEquiv _ _ a.unit

/-- 概要：随伴の余単位を h Fun(Y,Y) で取り出す。
方針：二胞体の表示同値を使う。規約：余単位を可逆としない。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK）。 -/
def counitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ F)) : hoFunctor.obj ((ihom Y).obj Y)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Y)) :=
  qcatCellEquiv _ _ a.counit

/-- 概要：同じ左随伴の右随伴間の FunctorIso。
方針：mate で得た同型を A3a の型に移す。規約：h Fun 内の同型。
使われ方：Kerodon Remark 6.2.1.19（Tag 02F3）。 -/
def rightAdjointFunctorIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G G' : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F G') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G G' := qcatIsoToFunctorIso (rightAdjointIso a b)

/-- 概要：同じ右随伴の左随伴間の FunctorIso。
方針：mate の逆同型を A3a の型に移す。規約：h Fun 内の同型。
使われ方：Kerodon §6.1.3（Tag 02D4）。 -/
def leftAdjointFunctorIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (b : QCatAdjunction F' G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F F' := qcatIsoToFunctorIso (leftAdjointIso a b)

/-- 概要：左三角恒等式を h Fun(X,Y) の等式として表示する。
方針：双圏の三角恒等式を Hom 圏の表示関手で写す。
規約：端点の単位子を明記し、単体集合の射の厳密な等式に強めない。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK） の (Z1)。 -/
@[kerodon 02EK]
lemma left_triangle_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (qcatHomFunctor X Y).map (Bicategory.leftZigzag a.unit a.counit) =
      (qcatHomFunctor X Y).map
        ((Bicategory.leftUnitor (qcatMap F)).hom ≫ (Bicategory.rightUnitor (qcatMap F)).inv) :=
  congrArg (qcatHomFunctor X Y).map a.left_triangle

/-- 概要：右三角恒等式を h Fun(Y,X) の等式として表示する。
方針：双圏の三角恒等式を Hom 圏の表示関手で写す。
規約：端点の単位子を明記する。
使われ方：Kerodon Def 6.2.1.1（Tag 02EK） の (Z2)。 -/
lemma right_triangle_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) :
    (qcatHomFunctor Y X).map (Bicategory.rightZigzag a.unit a.counit) =
      (qcatHomFunctor Y X).map
        ((Bicategory.rightUnitor (qcatMap G)).hom ≫ (Bicategory.leftUnitor (qcatMap G)).inv) :=
  congrArg (qcatHomFunctor Y X).map a.right_triangle

/-- 概要：任意のパラメータ quasicategory 上の二胞体の adjunct 対応。
方針：双圏の Hom 随伴と h Fun の表示同値を合成する。
規約：これは h Fun の Hom の全単射。写像空間そのものの同値は別途証明する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータを入れた証明の準備。 -/
def homEquiv {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (U : Z ⟶ X) (V : Z ⟶ Y) :
    ((SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (U ≫ F)) : hoFunctor.obj ((ihom Z).obj Y)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) ≃
    ((SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) : hoFunctor.obj ((ihom Z).obj X)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ G))) :=
  (qcatCellEquiv (U ≫ F) V).symm |>.trans
    ((Bicategory.Adjunction.homEquiv₂ a (g := qcatMap U) (h := qcatMap V)).trans
      (qcatCellEquiv U (V ≫ G)))

end QCatAdjunction
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.2.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointFunctorIso
attribute [cite HTT "5.2.2.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.comp
attribute [cite HTT "6.3.1.2" (partial := component) "仮定：同じ一方の関手に二つの ∞ 随伴（HTT より弱い：任意の準圏に適用でき、∞ トポス性と左完全性は不要）。結論：他方の随伴が FunctorIso で同値となる部分は一致。全随伴データの選択空間が可縮という高次の一意性まではこの二つの型には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.leftAdjointFunctorIso
attribute [cite HTT "6.3.1.2" (partial := component) "仮定：同じ一方の関手に二つの ∞ 随伴（HTT より弱い：任意の準圏に適用でき、∞ トポス性と左完全性は不要）。結論：他方の随伴が FunctorIso で同値となる部分は一致。全随伴データの選択空間が可縮という高次の一意性まではこの二つの型には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointFunctorIso
attribute [cite HTT "6.3.1.4" (partial := stronger-hyp) "仮定：二つの幾何学的射とその左随伴（Lean が強い：左随伴が有限極限だけでなく全小極限を保存すると仮定）。結論：同じ左随伴の合成は全小極限を保存し、逆順の右随伴の合成と実際の ∞ 随伴を成すため、この場合の幾何学的射の合成は一致。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.comp
