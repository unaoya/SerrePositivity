module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.AdjunctionFrameHomBifunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialFrameFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-!
概要：一般 Quillen 随伴の左像 frame と fibrant 終域置換を使う、同じ二変数の Kan Hom 同型。
方針：元の置換・frame を保持し、左 Quillen による frame 保存と右像の fibrancy を証明する。
規約：SSet のモデル構造の存在は仮定しない。使われ方：導来 ∞ 随伴への実際の Hom 入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u vC vD
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type vC} [Category.{u} C] [ModelCategory C]
  {D : Type vD} [Category.{u} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (P : CosimplicialFrameFamily (C := C)) (Q : C ⥤ C)
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations D) (fibrations D))

/-- 元の始域置換と終域 fibrant 置換を含む、両変数に自然な実際の frame Hom 随伴同型。 -/
def quillenReplacedFrameHomIso :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionLeftFrameHom (L := L) (Q ⋙ P.obj) (fibrantTarget fib) ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionRightFrameHom (R := R) (Q ⋙ P.obj) (fibrantTarget fib) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionFrameHomBifunctorIso adj (Q ⋙ P.obj) (fibrantTarget fib)

include adj in
/-- 左像 frame の Reedy cofibrancy は Quillen 条件から得られる。 -/
lemma quillenReplacedFrame_reedyCofibrant (X : C) :
    reedyLeft simplex (cofibrations D) (initial.to (P.obj.obj (Q.obj X) ⋙ L)) := by
  have := adj.isLeftAdjoint
  exact leftQuillen_frame_reedyCofibrant L _ (P.cofibrant (Q.obj X))

/-- 左像 frame の全構造射も弱同値であり、追加の frame 仮定を要しない。 -/
lemma quillenReplacedFrame_homotopicallyConstant (X : C) {n m : SimplexCategory}
    (f : n ⟶ m) : weakEquivalences D ((P.obj.obj (Q.obj X) ⋙ L).map f) :=
  leftQuillen_frame_homotopicallyConstant L _ (P.cofibrant (Q.obj X))
    (P.homotopicallyConstant (Q.obj X)) f

/-- cofibrant 始域への元の augmentation の左像も、各次数で同じ弱同値である。 -/
lemma quillenReplacedFrame_augmentation_weakEquivalence (hQ : ∀ X, IsCofibrant (Q.obj X))
    (X : C) (n : SimplexCategory) :
    weakEquivalences D ((Functor.whiskerRight (P.augmentation.app (Q.obj X)) L).app n) := by
  have := hQ X
  exact leftQuillen_frame_augmentation_weakEquivalence L _ (P.cofibrant (Q.obj X))
    (P.augmentation.app (Q.obj X)) (P.weak (Q.obj X)) n

include adj in
/-- 左 Quillen 条件の随伴側から、元の fibrant 終域置換の右像の fibrancy が従う。 -/
lemma quillenReplacedFrame_rightTarget_isFibrant (Y : D) :
    IsFibrant (R.obj ((fibrantTarget fib).obj Y)) := by
  have := adj.isRightAdjoint
  have := SerrePositivity.Quillen.isRightQuillen_of_isLeftQuillen adj
  have := fibrantTarget_isFibrant fib Y
  exact SerrePositivity.Quillen.isFibrant_obj R _

include adj in
/-- 左像 frame と元の fibrant 終域置換による実際の Hom は Kan。 -/
lemma quillenReplacedFrame_leftHom_kanComplex (X : Cᵒᵖ) (Y : D) :
    KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionLeftFrameHom (L := L) (Q ⋙ P.obj) (fibrantTarget fib)).obj X).obj Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact cosimplicialHom_kanComplex (P.obj.obj (Q.obj X.unop) ⋙ L)
    (quillenReplacedFrame_reedyCofibrant adj P Q X.unop)
    (quillenReplacedFrame_homotopicallyConstant P Q X.unop) _

include adj in
/-- 元の frame と終域置換の右像による同じ Hom も Kan。 -/
lemma quillenReplacedFrame_rightHom_kanComplex (X : Cᵒᵖ) (Y : D) :
    KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionRightFrameHom (R := R) (Q ⋙ P.obj) (fibrantTarget fib)).obj X).obj Y) := by
  have := quillenReplacedFrame_rightTarget_isFibrant adj fib Y
  exact cosimplicialHom_kanComplex (P.obj.obj (Q.obj X.unop))
    (P.cofibrant (Q.obj X.unop)) (P.homotopicallyConstant (Q.obj X.unop))
    (R.obj ((fibrantTarget fib).obj Y))

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
