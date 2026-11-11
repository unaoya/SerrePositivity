module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCompositionTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyPathParameters

/-!
概要：指定した単位三角形の輸送をパラメータの射で制限する。
方針：普遍三角形の前合成と境界 path の厳密な自然性を照合する。
規約：制限後に輸送を選び直さず、元の輸送の図式そのものを保持する。
使われ方：B1 の導来 fiber の普遍族で選んだ復元の前合成。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：基準単位三角形の族はパラメータ前合成と厳密に可換。
方針：一つの普遍三角形への前合成の合成則を使う。
規約：族ごとに三角形を選び直さない。
使われ方：制限した輸送の始点の認識。 -/
lemma unitIntervalCompositionTriangle_family_precomp {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y (i ≫ f)).diagram =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f).diagram ≫ (pre i).app X := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family_diagram, pre_map, NatTrans.comp_app, Category.assoc]

section
variable {A B X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
variable (x : X _⦋0⦌) (y : Y _⦋0⦌) (i : A ⟶ B)
variable (f₀ : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
variable (f₁ : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
variable {g₀ : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)}
variable {g₁ : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)}
variable (H₀ : SSet.Homotopy (f₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y) g₀)
variable (H₁ : SSet.Homotopy (f₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y) g₁)
variable (hf : i ≫ f₁ = f₀)
variable (hH : H₀.h = (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h)
include hf hH

/-- 概要：指定ホモトピーを保持した単位三角形の境界 path は前合成と可換。
方針：二つの固定辺では定値 path の自然性、対角辺では族の path の自然性を使う。
規約：標的族と raw なホモトピーの一致を明示的に受け取る。
使われ方：普遍族の輸送を制限しても指定境界 path を保つことの確認。 -/
lemma unitCompositionBoundaryPath_precomp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₁ H₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀ := by
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₁).diagram ≫ (pre i).app X =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₀).diagram := by
    rw [← unitIntervalCompositionTriangle_family_precomp, hf]
  apply boundary.hom_ext
  intro j
  fin_cases j
  · change boundary.ι (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₁ H₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) = boundary.ι (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀
    have hb : boundary.ι (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₁ H₁ =
        stdSimplex.δ (0 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₁).diagram ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryPath_face_zero _ _ _ _
    have ha : boundary.ι (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀ =
        stdSimplex.δ (0 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₀).diagram ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryPath_face_zero _ _ _ _
    rw [← Category.assoc, hb, ha]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalencePathRefl_map, reassoc_of% ht]
  · change boundary.ι (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₁ H₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) = boundary.ι (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath_diagonal, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath_diagonal]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyPath_precomp i H₀ H₁ hH
  · change boundary.ι (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₁ H₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) = boundary.ι (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀
    have hb : boundary.ι (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₁ H₁ =
        stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₁).diagram ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryPath_face_two _ _ _ _
    have ha : boundary.ι (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀ =
        stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₀).diagram ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundaryPath_face_two _ _ _ _
    rw [← Category.assoc, hb, ha]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.equivalencePathRefl_map, reassoc_of% ht]

/-- 概要：普遍パラメータ上で選んだ三角形輸送を、同じ始点・境界 path のまま制限する。
方針：元の輸送の図式を前合成の可逆 path 写像へ写し、始点と境界の自然性を使う。
規約：制限後の輸送を独立に選び直さない。
使われ方：B1 の戻る比較射の前合成を元の族上で検証する。 -/
noncomputable def unitCompositionPathExtension_precomp :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorDiagramPathExtension (boundary 2).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionBoundaryPath η x y f₀ H₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalCompositionTriangle_family η x y f₀).diagram where
  diagram := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionPathExtension η x y f₁ H₁).diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X)
  restriction := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionPathExtension η x y f₁ H₁).restriction]
    exact unitCompositionBoundaryPath_precomp η x y i f₀ f₁ H₀ H₁ hf hH
  start := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCompositionPathExtension η x y f₁ H₁).start,
      ← unitIntervalCompositionTriangle_family_precomp, hf]

end

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
