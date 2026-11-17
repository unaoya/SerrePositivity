module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRepresentableCells
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones

/-!
概要：BK自由細胞に任意の単体集合をテンソルし、終頂点の生成元で全射を表示する。
方針：同じ非退化射列の定値単体集合を使い、最後の射による輸送で降下射を記述。
規約：IS-W2 R03aの自由境界付着の証明分割。SSetのモデル構造を仮定しない。
使われ方：各自由境界の持ち上げを全BK細胞の持ち上げへ束ねる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DiagramModel _root_.SerrePositivity.DiagramModel.BousfieldKanCells
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 自由細胞の添字を定値単体集合として読む同じ図式。 -/
def bkCellWeight (n : ℕ) : I ⥤ SSet.{u} :=
  freeCellDiagram I n ⋙ Functor.const SimplexCategoryᵒᵖ

/-- 同じ全自由細胞に単体集合をテンソルする全関手。 -/
def bkCellTensor (n : ℕ) : SSet.{u} ⥤ I ⥤ SSet.{u} :=
  WeightedCones.tensorDiagram I (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellWeight I n)

/-- 各射列の終頂点に置く同じ標準生成元。 -/
def bkCellGenerator {n : ℕ} (c : (nerve I).nonDegenerate n) (X : SSet.{u}) :
    X ⟶ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X).obj (c.val.obj (Fin.last n)) where
  app _ := ↾fun x => (x, ⟨c, 𝟙 _⟩)
  naturality _ _ _ := rfl

/-- 生成元は元の単体集合の全射で自然。 -/
theorem bkCellGenerator_naturality {n : ℕ} (c : (nerve I).nonDegenerate n)
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c X ≫ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).map f).app (c.val.obj (Fin.last n)) =
      f ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c Y := rfl

/-- 終頂点の生成元の値から作る、同じ全自由細胞からの降下射。 -/
def bkCellDesc {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X ⟶ Z where
  app i :=
    { app d := ↾fun s => (Z.map s.2.2).app d ((f s.2.1).app d s.1)
      naturality d e α := by
        apply ConcreteCategory.hom_ext
        rintro ⟨x, c, g⟩
        change (Z.map g).app e ((f c).app e (X.map α x)) =
          (Z.obj i).map α ((Z.map g).app d ((f c).app d x))
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply] }
  naturality i j g := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨x, c, h⟩
    change (Z.map (h ≫ g)).app d ((f c).app d x) =
      (Z.map g).app d ((Z.map h).app d ((f c).app d x))
    rw [Z.map_comp]
    rfl

/-- 降下射は元の終頂点の同じ標準生成元を保つ。 -/
theorem bkCellGenerator_desc {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n)))
    (c : (nerve I).nonDegenerate n) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c X ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc I X Z f).app (c.val.obj (Fin.last n)) = f c := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  change (Z.map (𝟙 _)).app d ((f c).app d x) = (f c).app d x
  rw [Z.map_id]
  rfl

/-- 全自由細胞からの射は、同じ終頂点の標準生成元で一意に決まる。 -/
theorem bkCellDesc_unique {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n)))
    (m : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X ⟶ Z)
    (hm : ∀ c, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c X ≫ m.app (c.val.obj (Fin.last n)) = f c) :
    m = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc I X Z f := by
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, c, g⟩
  let z : (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X).obj (c.val.obj (Fin.last n))).obj d :=
    (x, ⟨c, 𝟙 _⟩)
  have ht := ConcreteCategory.congr_hom (NatTrans.congr_app (m.naturality g) d) z
  change (m.app i).app d (x, ⟨c, (𝟙 _) ≫ g⟩) =
    (Z.map g).app d ((m.app (c.val.obj (Fin.last n))).app d (x, ⟨c, 𝟙 _⟩)) at ht
  rw [Category.id_comp] at ht
  have hv := ConcreteCategory.congr_hom (NatTrans.congr_app (hm c) d) x
  change (m.app (c.val.obj (Fin.last n))).app d (x, ⟨c, 𝟙 _⟩) = (f c).app d x at hv
  exact ht.trans (congrArg ((Z.map g).app d) hv)

/-- 標準生成元での一致は、同じ全自由細胞図式の射の一致を与える。 -/
theorem bkCellHom_ext {n : ℕ} {X : SSet.{u}} {Z : I ⥤ SSet.{u}}
    {m m' : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).obj X ⟶ Z}
    (h : ∀ c, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c X ≫ m.app (c.val.obj (Fin.last n)) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellGenerator I c X ≫ m'.app (c.val.obj (Fin.last n))) : m = m' :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc_unique I X Z _ m h).trans
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellDesc_unique I X Z _ m' (fun _ => rfl)).symm

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
