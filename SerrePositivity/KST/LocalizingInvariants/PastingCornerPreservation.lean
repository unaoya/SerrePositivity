module

public import SerrePositivity.KST.LocalizingInvariants.PastingOuterColimitReplacement
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality

/-!
概要：五頂点図式を保つ延長は左四角形と下側の合成三角形を保つ。
方針：両形状を五頂点部分複体へ持ち上げ、制限射の等式を前合成する。
規約：全単体上の等式。使われ方：反転した graph 長方形の指定射を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma pastingSquare_left_eq_of_corner_eq {X : SSet.{u}}
    {F G : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ G) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 2 := by
  exact congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso.hom ≫
    Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner) ≫ t) h

def pastingBottomToCorner : (Δ[2] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) :=
  Subcomplex.lift
    (lift (𝟙 Δ[2]) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) (by
      intro n s hs
      obtain ⟨t, rfl⟩ := hs
      intro j hx
      change (0 : Fin 2) ≠ 1
      decide)

lemma pastingBottomTriangle_eq_of_corner_eq {X : SSet.{u}}
    {F G : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ G) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle G :=
  congrArg (fun t => pastingBottomToCorner ≫ t) h

lemma reverseGrid_bottomTriangle {X : SSet.{u}}
    (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.KST.LocalizingInvariants
