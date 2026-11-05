module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryHom

/-!
概要：射影の相対始対象二つは、その像の同型から元の圏でも同型になる。
方針：両始点の Hom 全単射で順射・逆射を持ち上げ、忠実性で逆恒等式を示す。
規約：射影全体の充満忠実性は仮定しない。使われ方：K-8 の核と本質像の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

def relativeInitialVertexIso (p : X ⟶ Y) (x y : X _⦋0⦌)
    (hx : InitialBoundaryLifting p x) (hy : InitialBoundaryLifting p y)
    (e : VertexIso (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) :
    VertexIso x y := by
  let f := (hoFunctor.map p).toFunctor
  have hxy := SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p x y hx
  have hyx := SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p y x hy
  let a := Classical.choose (hxy.surjective e.hom)
  let b := Classical.choose (hyx.surjective e.inv)
  have ha := Classical.choose_spec (hxy.surjective e.hom)
  have hb := Classical.choose_spec (hyx.surjective e.inv)
  refine ⟨a, b, ?_, ?_⟩
  · apply (SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p x x hx).injective
    change f.map (a ≫ b) = f.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (congrArg₂ (fun u v => u ≫ v) ha hb).trans e.hom_inv_id
  · apply (SerrePositivity.InfinityCategories.F1B.hoFunctorMap_bijective_of_initialBoundary p y y hy).injective
    change f.map (b ≫ a) = f.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (congrArg₂ (fun u v => u ≫ v) hb ha).trans e.inv_hom_id

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso._proof_2 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso._proof_3 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso._proof_4 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso._proof_5 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.relativeInitialVertexIso._proof_6 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.relativeInitialVertexIso._proof_6
