module
public import SerrePositivity.KST.SConstruction.IdentitySimplexFibers
public import SerrePositivity.KST.SConstruction.TensorElementsResolution

/-! # 左 fiber のパラメーターを保った積との比較
概要：f の単体 fiber から恒等射の単体 fiber と Z の積へ送る。
方針：f と g を第一射影に合成し、元のパラメーターを厳密に保つ。
規約：元の射への比較を他の augmentation に置換しない。使われ方：単体積版 Quillen A。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 左 fiber から恒等射の左 fiber へ、元のパラメーターを保って送る。 -/
def simplexFiberIdentityMap {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌) :
    simplexLeftFiber f y ⟶ simplexLeftFiber (𝟙 Y) y :=
  simplexLeftFiberLift (𝟙 Y) y (simplexLeftFiberProjection f y ≫ f)
    (simplexLeftFiberParameter f y) (by
      rw [Category.comp_id]
      exact simplexLeftFiber_condition f y)

/-- 恒等射の左 fiber への比較は単体圏上で自然。 -/
def simplexFiberIdentityComparison {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplexFiberDiagram f ⟶ simplexFiberDiagram (𝟙 Y) where
  app a := simplexFiberIdentityMap f a.unop.val
  naturality {a b} h := by
    apply simplexLeftFiber_hom_ext (𝟙 Y) b.unop.val
    · change simplexFiberDiagramMap f h ≫ simplexFiberIdentityMap f b.unop.val ≫
          simplexLeftFiberProjection (𝟙 Y) b.unop.val =
        (simplexFiberIdentityMap f a.unop.val ≫ simplexFiberDiagramMap (𝟙 Y) h) ≫
          simplexLeftFiberProjection (𝟙 Y) b.unop.val
      rw [simplexFiberIdentityMap, simplexLeftFiberLift_projection,
        ← Category.assoc, simplexFiberDiagramMap_projection, Category.assoc,
        simplexFiberDiagramMap_projection, simplexFiberIdentityMap,
        simplexLeftFiberLift_projection]
    · change simplexFiberDiagramMap f h ≫ simplexFiberIdentityMap f b.unop.val ≫
          simplexLeftFiberParameter (𝟙 Y) b.unop.val =
        (simplexFiberIdentityMap f a.unop.val ≫ simplexFiberDiagramMap (𝟙 Y) h) ≫
          simplexLeftFiberParameter (𝟙 Y) b.unop.val
      rw [simplexFiberIdentityMap, simplexLeftFiberLift_parameter,
        simplexFiberDiagramMap_parameter, Category.assoc, simplexFiberDiagramMap_parameter,
        ← Category.assoc, simplexFiberIdentityMap, simplexLeftFiberLift_parameter]

/-- 各左 fiber から恒等射の左 fiber と Z の積への比較。 -/
def simplexFiberProductComparison {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    simplexFiberDiagram f ⟶ tensorCoefficientDiagram (simplexFiberDiagram (𝟙 Y)) Z where
  app a := CartesianMonoidalCategory.lift (simplexFiberIdentityMap f a.unop.val)
    (simplexLeftFiberProjection f a.unop.val ≫ g)
  naturality {a b} h := by
    apply CartesianMonoidalCategory.hom_ext
    · change (simplexFiberDiagram f).map h ≫
          (CartesianMonoidalCategory.lift _ _ ≫ CartesianMonoidalCategory.fst _ _) =
        (CartesianMonoidalCategory.lift _ _ ≫
          ((simplexFiberDiagram (𝟙 Y)).map h ▷ Z)) ≫ CartesianMonoidalCategory.fst _ _
      simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst_assoc]
      exact (simplexFiberIdentityComparison f).naturality h
    · change (simplexFiberDiagram f).map h ≫
          (CartesianMonoidalCategory.lift _ _ ≫ CartesianMonoidalCategory.snd _ _) =
        (CartesianMonoidalCategory.lift _ _ ≫
          ((simplexFiberDiagram (𝟙 Y)).map h ▷ Z)) ≫ CartesianMonoidalCategory.snd _ _
      simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        CartesianMonoidalCategory.lift_snd]
      change simplexFiberDiagramMap f h ≫
        (simplexLeftFiberProjection f b.unop.val ≫ g) = _
      rw [← Category.assoc, simplexFiberDiagramMap_projection]

/-- 左 fiber から Z への比較が局所化同型なら、パラメーターを残した比較も局所化同型。 -/
lemma simplexFiberProductComparison_localized_isIso {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z)
    (hf : ∀ (m : ℕ) (y : Y _⦋m⦌), IsIso (AnodyneHomotopy.anodyneQ.map
      (simplexLeftFiberProjection f y ≫ g))) (a : Y.Elementsᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((simplexFiberProductComparison f g).app a)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hs : IsIso (Q.map (CartesianMonoidalCategory.snd
      ((simplexFiberDiagram (𝟙 Y)).obj a) Z)) :=
    identitySimplexFiber_snd_localized_isIso Y Z a.unop.val
  have he : (simplexFiberProductComparison f g).app a ≫
      CartesianMonoidalCategory.snd _ Z = simplexLeftFiberProjection f a.unop.val ≫ g :=
    CartesianMonoidalCategory.lift_snd _ _
  have hi : IsIso (Q.map ((simplexFiberProductComparison f g).app a) ≫
      Q.map (CartesianMonoidalCategory.snd _ Z)) := by
    rw [← Q.map_comp, he]
    exact hf a.unop.obj.unop.len a.unop.val
  exact (isIso_comp_right_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
