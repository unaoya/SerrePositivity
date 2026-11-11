module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointFamilyChoice
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection

/-!
概要：固定した二つの関手圏で、逆向きの右関手族を単位の図式に接続する母単体集合。
方針：標準単体の twisted arrow 上で両端を評価し、指定射影への持ち上げを保持する。
規約：core に制限せず、quasicategory 性や射影の同値性はここでは主張しない。
使われ方：二対象の全自然変換を含む随伴対応の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：反対圏値の族を、始域を反転した元の圏値の族に戻す。
方針：射を反転して二重反転の標準同型を合成する。
規約：単体集合の厳密な射を保持する。
使われ方：右随伴族の反変評価。 -/
def unopPairFamily {K B : SSet.{u}} (r : K ⟶ B.op) : K.op ⟶ B :=
  SSet.opFunctor.map r ≫ (SSet.opFunctorCompOpFunctorIso.app B).hom

/-- 概要：反変評価はパラメータの制限と両立する。
方針：反転関手の合成保存を使う。
規約：同型までではなく射の等式。
使われ方：面・退化写像の定義。 -/
lemma unopPairFamily_pre {K K' B : SSet.{u}} (f : K' ⟶ K) (r : K ⟶ B.op) :
    unopPairFamily (f ≫ r) = SSet.opFunctor.map f ≫ unopPairFamily r := by
  simp only [unopPairFamily, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：twisted arrow の両端から、順向きの左族と逆向きの右族を共同評価する。
方針：右端で左族、左端で右族を評価する。
規約：全自然変換を許す任意の単体集合に定義する。
使われ方：単位の可換図式の底。 -/
def twistedPairDiagram {K A B : SSet.{u}} (l : K ⟶ A) (r : K ⟶ B.op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow K ⟶ A ⊗ B :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K ≫ l) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft K ≫ unopPairFamily r)

/-- 概要：共同評価は全てのパラメータの射に厳密に自然。
方針：twisted arrow の両端の自然性を積で束ねる。
規約：高次単体を選び直さない。
使われ方：母空間を一つの単体集合にする。 -/
lemma twistedPairDiagram_pre {K K' A B : SSet.{u}} (f : K' ⟶ K)
    (l : K ⟶ A) (r : K ⟶ B.op) :
    twistedPairDiagram (f ≫ l) (f ≫ r) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ≫ twistedPairDiagram l r := by
  unfold twistedPairDiagram
  rw [comp_lift]
  congr 1

/-- 概要：二つの族と twisted arrow 上の指定射影への持ち上げを保持する単体。
方針：底の共同評価との厳密な可換条件を付ける。
規約：持ち上げの全単体データを保持し、存在命題に切り詰めない。
使われ方：固定二対象の単位対応の母単体集合。 -/
structure TwistedPairLiftSimplex {A B S T : SSet.{u}} (q : S ⟶ T)
    (b : A ⊗ B ⟶ T) (n : SimplexCategory) where
  left : stdSimplex.obj n ⟶ A
  right : stdSimplex.obj n ⟶ B.op
  unit : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow (stdSimplex.obj n) ⟶ S
  condition : unit ≫ q = twistedPairDiagram left right ≫ b

/-- 概要：同じ三つの実際の族を持つ単体は等しい。
方針：可換条件の証明の一意性を使う。
規約：左右の関手族と単位族を比較する。
使われ方：面・退化写像の関手則。 -/
@[ext] lemma TwistedPairLiftSimplex.ext {A B S T : SSet.{u}} {q : S ⟶ T}
    {b : A ⊗ B ⟶ T} {n : SimplexCategory} (x y : TwistedPairLiftSimplex q b n)
    (hl : x.left = y.left) (hr : x.right = y.right) (hu : x.unit = y.unit) : x = y := by
  cases x
  cases y
  cases hl
  cases hr
  cases hu
  rfl

/-- 概要：指定単体の制限は元の三つの族の前合成。
方針：共同評価の自然性で可換条件を引き戻す。
規約：全ての単体作用に同じ構成を使う。
使われ方：母空間の面・退化写像。 -/
def TwistedPairLiftSimplex.restrict {A B S T : SSet.{u}} {q : S ⟶ T}
    {b : A ⊗ B ⟶ T} {n m : SimplexCategory} (x : TwistedPairLiftSimplex q b n)
    (f : m ⟶ n) : TwistedPairLiftSimplex q b m where
  left := SSet.stdSimplex.map f ≫ x.left
  right := SSet.stdSimplex.map f ≫ x.right
  unit := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (SSet.stdSimplex.map f) ≫ x.unit
  condition := by
    rw [Category.assoc, x.condition, twistedPairDiagram_pre, Category.assoc]

/-- 概要：順向き・逆向きの二つの全関手族と単位図式の母単体集合。
方針：twisted arrow 上の実持ち上げの制限を面・退化写像にする。
規約：充填性と射影の同値性は別に証明する。
使われ方：対ごとの随伴双対性の対応空間の入力。 -/
def twistedPairLift {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T) : SSet.{u} where
  obj n := TwistedPairLiftSimplex q b n.unop
  map f := ↾fun x ↦ x.restrict f.unop
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    apply TwistedPairLiftSimplex.ext
    · simp [TwistedPairLiftSimplex.restrict]
    · simp [TwistedPairLiftSimplex.restrict]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (SSet.stdSimplex.map (𝟙 n.unop)) ≫ x.unit = _
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply TwistedPairLiftSimplex.ext
    · simp [TwistedPairLiftSimplex.restrict, Category.assoc]
    · simp [TwistedPairLiftSimplex.restrict, Category.assoc]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (SSet.stdSimplex.map (g.unop ≫ f.unop)) ≫
        x.unit = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (SSet.stdSimplex.map g.unop) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (SSet.stdSimplex.map f.unop) ≫ x.unit)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：対応単体から順向きの元の左族を取り出す単体写像。
方針：標準単体からの射の Yoneda 表示を使う。
規約：全自然変換を含む始域 A に着地する。
使われ方：対ごとの双対性の左射影。 -/
def twistedPairLiftLeft {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T) :
    twistedPairLift q b ⟶ A where
  app _ := ↾fun x ↦ SSet.yonedaEquiv x.left
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (SSet.yonedaEquiv_naturality f.unop x.left).symm

/-- 概要：対応単体から逆向きの元の右族を取り出す単体写像。
方針：右族の Yoneda 表示を使う。
規約：core ではなく全圏 B の反対に着地する。
使われ方：対ごとの双対性の右射影。 -/
def twistedPairLiftRight {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T) :
    twistedPairLift q b ⟶ B.op where
  app _ := ↾fun x ↦ SSet.yonedaEquiv x.right
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (SSet.yonedaEquiv_naturality f.unop x.right).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
