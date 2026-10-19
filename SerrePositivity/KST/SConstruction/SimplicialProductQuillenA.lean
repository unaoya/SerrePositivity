module
public import SerrePositivity.KST.SConstruction.SimplexFiberProductComparison
public import SerrePositivity.KST.SConstruction.FiberResolutionAugmentation

/-! # 単体積版 Quillen A
概要：各 Y 単体上の左 fiber から Z への局所化同型から、X→Y×Z の局所化同型を得る。
方針：左 fiber 解消を恒等射の左 fiber と Z の積の解消に比較する。
規約：元の射との可換性を厳密に照合し、モデル圏を仮定しない。使われ方：object S• の加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open SerrePositivity.SimplicialModel SerrePositivity.BisimplicialModel
open scoped Simplicial

/-- 左 fiber の解消から、Y と Z の積へのパラメーターを保持する比較。 -/
def simplexFiberResolutionProductMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    diagonal.obj (elementsResolution (simplexFiberDiagram f)) ⟶ Y ⊗ Z :=
  diagonal.map (elementsResolutionMap (simplexFiberProductComparison f g)) ≫
    tensorElementsResolutionComparison (simplexFiberDiagram (𝟙 Y)) Z ≫
      (fiberResolutionAugmentation (𝟙 Y) ▷ Z)

/-- 解消から積への比較は、元の射対 (f,g) と augmentation の合成そのもの。 -/
lemma simplexFiberResolutionProductMap_eq {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    simplexFiberResolutionProductMap f g =
      fiberResolutionAugmentation f ≫ CartesianMonoidalCategory.lift f g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro c
  apply Prod.ext
  · let e := (c.obj 0).unop
    change (simplexLeftFiberProjection (𝟙 Y) e.obj.unop.val).app n
      ((simplexFiberIdentityMap f e.obj.unop.val).app n e.val) =
      f.app n ((simplexLeftFiberProjection f e.obj.unop.val).app n e.val)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (simplexLeftFiberLift_projection (𝟙 Y) e.obj.unop.val
        (simplexLeftFiberProjection f e.obj.unop.val ≫ f)
        (simplexLeftFiberParameter f e.obj.unop.val) _) n) e.val
  · change g.app n (fiberResolutionValue f (c.obj (Fin.last n.unop.len)).unop) =
      g.app n (fiberResolutionValue f (c.obj 0).unop)
    exact congrArg (g.app n) (fiberResolutionValue_map f
      (c.map (homOfLE (Fin.zero_le (Fin.last n.unop.len)))).unop)

/-- 各左 fiber の Z への比較が局所化同型なら、解消から積への比較も局所化同型。 -/
lemma simplexFiberResolutionProductMap_localized_isIso {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z)
    (hf : ∀ (m : ℕ) (y : Y _⦋m⦌), IsIso (AnodyneHomotopy.anodyneQ.map
      (simplexLeftFiberProjection f y ≫ g))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (simplexFiberResolutionProductMap f g)) := by
  have := elementsResolutionMap_diagonal_localized_isIso (simplexFiberProductComparison f g)
    (simplexFiberProductComparison_localized_isIso f g hf)
  have : IsIso (tensorElementsResolutionComparison (simplexFiberDiagram (𝟙 Y)) Z) :=
    (tensorElementsResolutionIso (simplexFiberDiagram (𝟙 Y)) Z).isIso_hom
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso
    (fiberResolutionAugmentation (𝟙 Y)) (fiberResolutionAugmentation_localized_isIso (𝟙 Y)) Z
  rw [simplexFiberResolutionProductMap, AnodyneHomotopy.anodyneQ.map_comp,
    AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- 単体積版 Quillen A：各 Y 単体上の左 fiber から Z への弱同値は X→Y×Z の弱同値を与える。 -/
lemma simplicialProductQuillenA {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (hf : ∀ (m : ℕ) (y : Y _⦋m⦌), IsIso (AnodyneHomotopy.anodyneQ.map
      (simplexLeftFiberProjection f y ≫ g))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (CartesianMonoidalCategory.lift f g)) := by
  have := fiberResolutionAugmentation_localized_isIso f
  have hi := simplexFiberResolutionProductMap_localized_isIso f g hf
  rw [simplexFiberResolutionProductMap_eq, AnodyneHomotopy.anodyneQ.map_comp] at hi
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
