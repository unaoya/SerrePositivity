module

public import SerrePositivity.EInfinity.FrameHom.SourceRoofFamily
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofLeftIdentity

/-!
概要：source augmentation で表された元の射の実二列 roof を元の hammock 射へ正規化する。
方針：同じ augmentation を二列の縦射にした実ホモトピーを使う。
規約：元の射・元の roof と同じ単体的円柱を保持する。
使われ方：right frame の零単体比較と指定局所化の二胞体の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Opposite Hammock MonoidalCategory
open SerrePositivity.Reedy
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}
  (q : CofibrantResolution (C := C) simplex X) (n : SimplexCategory) (f : X ⟶ Y)

/-- 概要：元の射を source augmentation に前合成した同じ全要素の頂点。
方針：元の次数と元の合成を同じ要素圏へ入れる。
規約：Hom 宇宙だけを揃える。使われ方：実二列比較の零単体評価。 -/
def sourceFrameUnitElement :
    ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ :=
  op (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).elementsMk (op n) (q.augmentation.app n ≫ f))

/-- 概要：同じ元の要素の実二列 roof 像は同じ augmentation と合成の roof。
方針：同じ二列比較と同じ定値な零単体を評価する。
規約：元の零単体の厳密な等式。使われ方：元の射への実円柱の始端。 -/
lemma sourceFrameUnitElement_roof_zero :
    (resolutionLeftRoofColimitMap q Y).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (sourceFrameUnitElement q n f)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj (weakEquivalences C) (q.augmentation.app n)
          (q.augmentation_weakEquivalence n) (q.augmentation.app n ≫ f))).app (op ⦋0⦌)
            PUnit.unit := by
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word).app (op ⦋0⦌))
  let F := ComposableArrows.mk₀ (sourceFrameUnitElement q n f) ⋙
    ULiftHom.down.{0, v, max u v} ⋙ frameLeftRoofFunctor (weakEquivalences C)
      q.obj q.augmentation q.augmentation_weakEquivalence (fun a => q.homotopicallyConstant a)
  let G := (Functor.const (Fin 1)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj (weakEquivalences C)
    (q.augmentation.app n) (q.augmentation_weakEquivalence n) (q.augmentation.app n ≫ f))
  change F = G
  have ho : ∀ i, F.obj i = G.obj i := fun _ => rfl
  apply CategoryTheory.Functor.hext ho
  intro i j a
  obtain rfl : i = j := by fin_cases i; fin_cases j; rfl
  obtain rfl : a = 𝟙 i := Subsingleton.elim _ _
  simp only [F.map_id, G.map_id]
  rfl

/-- 概要：同じ augmentation と元の射の合成からなる roof を元の射へ実ホモトピーで戻す。
方針：同じ弱 augmentation を二列間の縦射とし恒等左脚へ送る。
規約：元の射を変えない。使われ方：零単体の coherent 正規化。 -/
def sourceFrameUnitRoofHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj (weakEquivalences C) (q.augmentation.app n)
        (q.augmentation_weakEquivalence n) (q.augmentation.app n ≫ f)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_leftIdentity] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.map (weakEquivalences C) (q.augmentation.app n)
      (q.augmentation_weakEquivalence n) (Category.comp_id _) rfl
      (g := f) (hq := (weakEquivalences C).id_mem X))

/-- 概要：同じ元の射の roof と元の射の一定全単体は反転後に一致する。
方針：同じ実円柱を anodyne 反転関手へ送る。
規約：元の比較射の全単体。使われ方：指定局所化への零単体三角形。 -/
lemma sourceFrameUnitRoof_Q :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj (weakEquivalences C) (q.augmentation.app n)
        (q.augmentation_weakEquivalence n) (q.augmentation.app n ≫ f))) =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f) :=
  AnodyneHomotopy.map_homotopy_eq _ (Localization.inverts _ SSet.anodyneExtensions)
    (sourceFrameUnitRoofHomotopy q n f)

end SerrePositivity.EInfinity.FrameHom
