module
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：全係数の要素圏と同じGrothendieck構成の係数表示を照合する。
方針：要素と底・単体次数を同じ順序に並べ、Homの宇宙だけを持ち上げる。
規約：元の底と係数の写像を保つ。
使われ方：元の全source frameの要素圏から同じ底上の分類への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ各係数の要素圏を、Homだけ宇宙uへ持ち上げた全図式。 -/
def simplicialElementsCatDiagram : I ⥤ Cat.{u,u} where
  obj i := Cat.of (ULiftHom.{u} (F.obj i).Elements)
  map f := (ULiftHom.down ⋙ (F.map f).mapElements ⋙ ULiftHom.up).toCatHom
  map_id i := by
    rw [F.map_id]
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  map_comp f g := by
    rw [F.map_comp]
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 元の二重添字の全要素圏。 -/
abbrev SimplicialTotalElements := (Functor.uncurry.obj F).Elements

/-- 同じ全要素圏の元の底への射影。 -/
def simplicialTotalElementsProjection : SimplicialTotalElements F ⥤ I :=
  Functor.Elements.π (Functor.uncurry.obj F) ⋙ CategoryTheory.Prod.fst I SimplexCategoryᵒᵖ
/-- 同じ要素圏の等式輸送の射は、元の単体次数の等式輸送を持つ。 -/
lemma uliftElements_eqToHom_hom {K : SSet.{u}} {x y : ULiftHom.{u} K.Elements}
    (h : x = y) : (eqToHom h).down.hom = eqToHom (congrArg (fun z => z.obj) h) := by
  cases h
  rfl

/-- 同じGrothendieckの要素を、元の全二重添字の要素へ並べ直す。 -/
def simplicialElementsGrothendieckForward :
    Grothendieck (simplicialElementsCatDiagram F) ⥤ SimplicialTotalElements F where
  obj X := { obj := (X.base, X.fiber.obj), val := X.fiber.val }
  map f := ⟨(f.base, f.fiber.down.hom), f.fiber.down.map_val⟩
  map_id X := by
    apply Functor.Elements.Hom.ext
    apply Prod.ext
    · rfl
    · change (Grothendieck.id X).fiber.down.hom = 𝟙 X.fiber.obj
      dsimp only [Grothendieck.id]
      rw [uliftElements_eqToHom_hom]
      rfl
  map_comp {X Y Z} f g := by
    apply Functor.Elements.Hom.ext
    apply Prod.ext
    · rfl
    · let π : ULiftHom.{u} (F.obj Z.base).Elements ⥤ SimplexCategoryᵒᵖ :=
        ULiftHom.down.{0,u,u} ⋙ Functor.Elements.π (F.obj Z.base)
      change π.map ((f ≫ g).fiber) = f.fiber.down.hom ≫ g.fiber.down.hom
      rw [Grothendieck.comp_fiber, π.map_comp, π.map_comp, eqToHom_map]
      change (𝟙 _) ≫ f.fiber.down.hom ≫ g.fiber.down.hom = _
      simp only [Category.id_comp]

/-- 同じ要素の底とfiberの並べ替え。 -/
def simplicialElementsGrothendieckObject (X : SimplicialTotalElements F) :
    Grothendieck (simplicialElementsCatDiagram F) :=
  ⟨X.obj.1, ULiftHom.objUp.{u,u} { obj := X.obj.2, val := X.val }⟩

/-- 元の要素の射を、同じ底の射と持ち上げたfiberの射へ並べ替える。 -/
def simplicialElementsGrothendieckHom {X Y : SimplicialTotalElements F} (f : X ⟶ Y) :
    simplicialElementsGrothendieckObject F X ⟶ simplicialElementsGrothendieckObject F Y :=
  { base := f.hom.1, fiber := ⟨⟨f.hom.2, f.map_val⟩⟩ }

/-- 元の二重添字の要素を、同じGrothendieckの底とfiberへ戻す。 -/
def simplicialElementsGrothendieckInverse :
    SimplicialTotalElements F ⥤ Grothendieck (simplicialElementsCatDiagram F) where
  obj := simplicialElementsGrothendieckObject F
  map := simplicialElementsGrothendieckHom F
  map_id X := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply ULift.ext
      apply Functor.Elements.Hom.ext
      rw [Grothendieck.id_fiber, uliftElements_eqToHom_hom]
      rfl
  map_comp {X Y Z} f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply ULift.ext
      apply Functor.Elements.Hom.ext
      let π : ULiftHom.{u} (F.obj Z.obj.1).Elements ⥤ SimplexCategoryᵒᵖ :=
        ULiftHom.down.{0,u,u} ⋙ Functor.Elements.π (F.obj Z.obj.1)
      change f.hom.2 ≫ g.hom.2 = π.map
        ((simplicialElementsGrothendieckHom F f ≫ simplicialElementsGrothendieckHom F g).fiber)
      rw [Grothendieck.comp_fiber, π.map_comp, π.map_comp, eqToHom_map]
      change f.hom.2 ≫ g.hom.2 = (𝟙 _) ≫ f.hom.2 ≫ g.hom.2
      simp only [Category.id_comp]

/-- 同じ全要素の二つの表示を、同じ並べ替えによる圏同値にする。 -/
def simplicialElementsGrothendieckEquivalence :
    Grothendieck (simplicialElementsCatDiagram F) ≌ SimplicialTotalElements F where
  functor := simplicialElementsGrothendieckForward F
  inverse := simplicialElementsGrothendieckInverse F
  unitIso := NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
    intro X Y f
    change f ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      apply ULift.ext
      apply Functor.Elements.Hom.ext
      rfl)
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
    intro X Y f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ f
    rw [Category.comp_id, Category.id_comp]
    apply Functor.Elements.Hom.ext
    rfl)
  functor_unitIso_comp X := by
    change (simplicialElementsGrothendieckForward F).map (𝟙 X) ≫ 𝟙 _ = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- 順方向の同じ並べ替えは、元の底への射影を厳密に保つ。 -/
theorem simplicialElementsGrothendieckForward_projection :
    simplicialElementsGrothendieckForward F ⋙ simplicialTotalElementsProjection F =
      Grothendieck.forget (simplicialElementsCatDiagram F) := rfl

/-- 逆方向も同じ底の射影を厳密に保つ。 -/
theorem simplicialElementsGrothendieckInverse_projection :
    simplicialElementsGrothendieckInverse F ⋙ Grothendieck.forget (simplicialElementsCatDiagram F) =
      simplicialTotalElementsProjection F := rfl
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
