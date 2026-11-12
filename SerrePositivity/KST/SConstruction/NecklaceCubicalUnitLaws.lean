module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalDayData
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInStructuralIso

/-! # 元の cubical 合成の左右単位則
概要：一点 necklace の実単位射が、mapping object 全体の合成の左右単位になる。
方針：強モノイダル関手の単位則と K 内の実単位同型を、全生成射上で照合する。
規約：元の単位・合成を使う。使われ方：cubical rigidification の豊穣圏構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet

/-- 元の各生成射の左に一点を合成すると、元の左単位を回収する。 -/
lemma necklaceCubicalDay_left_unit_cell {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    (necklaceCubicalDayIdentity K x ⊗ₘ necklaceCubicalDayCell T) ≫
        necklaceCubicalDayCompose K x x y =
      (λ_ (necklaceCubicalDay.obj T.necklace)).hom ≫ necklaceCubicalDayCell T := by
  have hc := necklaceCubicalDayCell_relation (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInLeftUnitor T).hom
  have hu := Functor.LaxMonoidal.left_unitality necklaceCubicalDay T.necklace
  let e : 𝟙_ CubicalDaySet.{u} ⟶ necklaceCubicalDay.obj _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint :=
    Functor.LaxMonoidal.ε necklaceCubicalDay.{u}
  let p : necklaceCubicalDay.obj _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint ⟶ necklaceCubicalDayMapping K x x :=
    necklaceCubicalDayCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)
  have hi : necklaceCubicalDayIdentity K x = e ≫ p := necklaceCubicalDayIdentity_unit K x
  have hm : (p ⊗ₘ necklaceCubicalDayCell T) ≫ necklaceCubicalDayCompose K x x y =
      Functor.LaxMonoidal.μ necklaceCubicalDay _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint T.necklace ≫
        necklaceCubicalDayCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) T) :=
    necklaceCubicalDayCompose_cell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) T
  have ht := (congrArg (fun b => b ≫ necklaceCubicalDayCompose K x x y)
    ((congrArg (fun b => b ⊗ₘ necklaceCubicalDayCell T) hi).trans
      (whiskerRight_comp_tensorHom e p (necklaceCubicalDayCell T)).symm)).trans
        (Category.assoc _ _ _)
  exact ht.trans ((congrArg (fun b => e ▷ necklaceCubicalDay.obj T.necklace ≫ b) hm).trans
    ((congrArg (fun b => e ▷ necklaceCubicalDay.obj T.necklace ≫
      Functor.LaxMonoidal.μ necklaceCubicalDay _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint T.necklace ≫ b) hc.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun b => b ≫ necklaceCubicalDayCell T) hu.symm))))

/-- 元の各生成射の右に一点を合成すると、元の右単位を回収する。 -/
lemma necklaceCubicalDay_right_unit_cell {K : SSet.{u}} {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    (necklaceCubicalDayCell T ⊗ₘ necklaceCubicalDayIdentity K y) ≫
        necklaceCubicalDayCompose K x y y =
      (ρ_ (necklaceCubicalDay.obj T.necklace)).hom ≫ necklaceCubicalDayCell T := by
  have hc := necklaceCubicalDayCell_relation (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInRightUnitor T).hom
  have hu := Functor.LaxMonoidal.right_unitality necklaceCubicalDay T.necklace
  let e : 𝟙_ CubicalDaySet.{u} ⟶ necklaceCubicalDay.obj _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint :=
    Functor.LaxMonoidal.ε necklaceCubicalDay.{u}
  let p : necklaceCubicalDay.obj _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint ⟶ necklaceCubicalDayMapping K y y :=
    necklaceCubicalDayCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y)
  have hi : necklaceCubicalDayIdentity K y = e ≫ p := necklaceCubicalDayIdentity_unit K y
  have hm : (necklaceCubicalDayCell T ⊗ₘ p) ≫ necklaceCubicalDayCompose K x y y =
      Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint ≫
        necklaceCubicalDayCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y)) :=
    necklaceCubicalDayCompose_cell T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K y)
  have ht := (congrArg (fun b => b ≫ necklaceCubicalDayCompose K x y y)
    ((congrArg (fun b => necklaceCubicalDayCell T ⊗ₘ b) hi).trans
      (whiskerLeft_comp_tensorHom (necklaceCubicalDayCell T) e p).symm)).trans
        (Category.assoc _ _ _)
  exact ht.trans ((congrArg (fun b => necklaceCubicalDay.obj T.necklace ◁ e ≫ b) hm).trans
    ((congrArg (fun b => necklaceCubicalDay.obj T.necklace ◁ e ≫
      Functor.LaxMonoidal.μ necklaceCubicalDay T.necklace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint ≫ b) hc.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun b => b ≫ necklaceCubicalDayCell T) hu.symm))))

/-- 元の mapping object 全体の左単位則。 -/
lemma necklaceCubicalDay_left_unit (K : SSet.{u}) (x y : K _⦋0⦌) :
    necklaceCubicalDayIdentity K x ▷ necklaceCubicalDayMapping K x y ≫
        necklaceCubicalDayCompose K x x y =
      (λ_ (necklaceCubicalDayMapping K x y)).hom := by
  apply (isColimitOfPreserves (tensorLeft (𝟙_ CubicalDaySet.{u}))
    (necklaceCubicalDayIsColimit K x y)).hom_ext
  intro T
  change (𝟙_ CubicalDaySet.{u}) ◁ necklaceCubicalDayCell T ≫ _ =
    (𝟙_ CubicalDaySet.{u}) ◁ necklaceCubicalDayCell T ≫ _
  rw [← Category.assoc, ← tensorHom_def', necklaceCubicalDay_left_unit_cell,
    leftUnitor_naturality]

/-- 元の mapping object 全体の右単位則。 -/
lemma necklaceCubicalDay_right_unit (K : SSet.{u}) (x y : K _⦋0⦌) :
    necklaceCubicalDayMapping K x y ◁ necklaceCubicalDayIdentity K y ≫
        necklaceCubicalDayCompose K x y y =
      (ρ_ (necklaceCubicalDayMapping K x y)).hom := by
  apply (isColimitOfPreserves (tensorRight (𝟙_ CubicalDaySet.{u}))
    (necklaceCubicalDayIsColimit K x y)).hom_ext
  intro T
  change necklaceCubicalDayCell T ▷ (𝟙_ CubicalDaySet.{u}) ≫ _ =
    necklaceCubicalDayCell T ▷ (𝟙_ CubicalDaySet.{u}) ≫ _
  rw [← Category.assoc, ← tensorHom_def, necklaceCubicalDay_right_unit_cell,
    rightUnitor_naturality]

end SerrePositivity.KST.SConstruction
