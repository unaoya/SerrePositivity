module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameComparison
public import SerrePositivity.EInfinity.OppositeFactorization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
概要：任意のモデル圏の関手的 right frame の元の Hom を束ねる。
方針：反対圏の同じ関手的解像を leftOp で戻し、共変 Hom を後合成する。
規約：単体集合のモデル構造は使わず、全対象・全作用素を保持する。
使われ方：指定された ∞ 局所化の pinched Hom との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：元の関手的な第二分解から同じ right frame の全族を作る。
方針：分解を反対化し、既存の関手的余単体解像へ渡す。
規約：モデル構造と分解以外の入力はない。使われ方：実 dg 代数への代入。 -/
def rightFrameFamilyOfFactorization
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    CofibrantResolutionFamily (C := Cᵒᵖ) simplex := by
  apply cosimplicialResolutionFamily
  rw [cofibrations_op, trivialFibrations_op]
  exact _root_.SerrePositivity.EInfinity.OppositeFactorization.opposite fib

variable (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ right frame を元の圏の単体的図式の族にする。
方針：元の解像の対象と自然変換を leftOp で戻す。
規約：全標的に厳密に自然。使われ方：Hom の全標的関手。 -/
def rightFrameDiagram : C ⥤ SimplexCategoryᵒᵖ ⥤ C where
  obj Y := (r.obj.obj (op Y)).leftOp
  map f := NatTrans.leftOp (r.obj.map f.op)
  map_id Y := by
    ext n
    change (((r.obj.map (𝟙 (op Y))).app n.unop).unop) = 𝟙 _
    rw [r.obj.map_id]
    rfl
  map_comp f g := by
    ext n
    change (((r.obj.map (g.op ≫ f.op)).app n.unop).unop) = _
    rw [r.obj.map_comp]
    rfl

/-- 概要：元の全標的から right frame への全自然な augmentation。
方針：同じ解像の augmentation の各成分を反転する。
規約：新たな置換は選ばない。使われ方：元の局所化射との零単体照合。 -/
def rightFrameUnit : Functor.const SimplexCategoryᵒᵖ ⟶ rightFrameDiagram r where
  app Y := NatTrans.leftOp (r.augmentation.app (op Y))
  naturality X Y f := by
    ext n
    apply Quiver.Hom.op_inj
    exact (congr_app (r.augmentation.naturality f.op) n.unop).symm

/-- 概要：元の射の定値単体集合を全標的で束ねる。
方針：定値単体図式へ同じ共変 Hom を後合成する。
規約：元の射を商にしない。使われ方：零単体の比較の基準。 -/
def ordinaryHomFamily (X : C) : C ⥤ SSet.{v} :=
  Functor.const SimplexCategoryᵒᵖ ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor X

/-- 概要：cofibrant 源から実 right frame への Hom 単体集合の全標的関手。
方針：元の図式へ共変 Hom を後合成する。
規約：対象は任意のモデル圏、全単体は元の圏の射。
使われ方：全標的に自然な導来 Hom 比較の始域。 -/
def rightFrameHom (X : C) : C ⥤ SSet.{v} :=
  rightFrameDiagram r ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor X

/-- 概要：元の全射を right frame Hom の全単体へ送る。
方針：同じ augmentation を Hom に後合成する。
規約：全標的に一つの自然変換。使われ方：局所化射の回収。 -/
def rightFrameHomUnit (X : C) : ordinaryHomFamily X ⟶ rightFrameHom r X :=
  Functor.whiskerRight (rightFrameUnit r) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor X)

/-- 概要：元の射は同じ augmentation との合成へ送られる。
方針：自然変換の定義を読む。
規約：零単体を含む全次数。使われ方：元の局所化射との照合。 -/
lemma rightFrameHomUnit_app (X Y : C) (n : SimplexCategoryᵒᵖ) (f : X ⟶ Y) :
    (((rightFrameHomUnit r X).app Y).app n) f =
      f ≫ ((rightFrameUnit r).app Y).app n := rfl

/-- 概要：実 Hom の n 単体は元の X から RⁿY への射。
方針：合成関手の定義を読む。
規約：定義上の一致。使われ方：全単体の比較射。 -/
lemma rightFrameHom_obj (X Y : C) (n : SimplexCategoryᵒᵖ) :
    ((rightFrameHom r X).obj Y).obj n =
      (X ⟶ ((rightFrameDiagram r).obj Y).obj n) := rfl

/-- 概要：right frame Hom の標的作用は元の射の後合成。
方針：共変 Hom の定義を読む。
規約：全標的射・全次数。使われ方：比較の全図式自然性。 -/
lemma rightFrameHom_map (X : C) {Y Z : C} (f : Y ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (a : X ⟶ ((rightFrameDiagram r).obj Y).obj n) :
    (((rightFrameHom r X).map f).app n) a =
      a ≫ ((rightFrameDiagram r).map f).app n := rfl

/-- 概要：right frame Hom は反対圏の同じ解像 Hom と同型。
方針：元の射を各次数で op にする。
規約：全単体作用素を保つ。使われ方：Kan 性の判定。 -/
def rightFrameHomOpIso (X Y : C) :
    (rightFrameHom r X).obj Y ≅
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (r.obj.obj (op Y))).obj (op X) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomIso X ((rightFrameDiagram r).obj Y)

/-- 概要：cofibrant 源からの元の right frame Hom は Kan 複体。
方針：反対源の fibrancy と同じ解像のホーン充填を使う。
規約：元の標的の fibrancy を要求しない。
使われ方：弱ホモトピー同値から QCat 同値への判定。 -/
lemma rightFrameHom_kanComplex (X : C) [IsCofibrant X] (Y : C) :
    SSet.KanComplex ((rightFrameHom r X).obj Y) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant X
  have := cosimplicialHom_kanComplex _ (r.cofibrant (op Y))
    (r.atObject (op Y)).homotopicallyConstant (op X)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso
    (rightFrameHomOpIso r X Y).symm

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
