module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.CommaSquareUncurry

/-!
概要：comma 正方形の族への逆表示とパラメータ前合成の厳密な公式。
方針：既存の族との全単射を使い、coherence と関手正方形の表示を照合する。
規約：パラメータの射は任意。新しいホモトピー代表を選ばない。
使われ方：B1 の時間付き正方形からホモトピーの両端を回収する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

section
variable {X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
variable {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} {A B : SSet.{u}}

/-- 概要：comma 正方形を区間写像空間の族へ戻す。
方針：正方形表示の全単射の逆を使う。
規約：側辺の代表を保持した厳密な逆表示。
使われ方：時間付き正方形から族のホモトピーを作る。 -/
noncomputable def UnitCommaFiberSquare.family (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace v w :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquareEquiv G x v w A).symm s

/-- 概要：族へ戻して展開すると元の正方形そのもの。
方針：全単射の両逆。
規約：coherence の raw な射も回収する。
使われ方：パラメータ制限の計算。 -/
lemma UnitCommaFiberSquare.family_square (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquare s.family = s :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquareEquiv G x v w A).apply_symm_apply s

/-- 概要：族を正方形にして戻すと元の族そのもの。
方針：全単射の左逆。
規約：射の厳密な等式。
使われ方：元の族を始点とする復元比較。 -/
lemma unitCommaFiberMappingSquare_family (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace v w) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquare f).family = f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquareEquiv G x v w A).left_inv f

/-- 概要：comma 正方形をパラメータの射で制限する。
方針：族に戻して前合成し、再び正方形へ展開する。
規約：全単射による操作で、代表を再選択しない。
使われ方：時間端点と普遍族の前合成。 -/
noncomputable def UnitCommaFiberSquare.precomp (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) (i : B ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w B := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquare (i ≫ s.family)

/-- 概要：正方形のパラメータ制限は族の前合成と厳密に可換。
方針：全単射の左逆。
規約：射の等式。
使われ方：時間付き正方形の族の両端。 -/
lemma UnitCommaFiberSquare.precomp_family (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) (i : B ⟶ A) :
    (s.precomp i).family = i ≫ s.family :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquareEquiv G x v w B).left_inv _

/-- 概要：パラメータ制限の標的図式は元の標的の前合成。
方針：区間の展開と標的の前合成自然性を使う。
規約：厳密な等式。
使われ方：時間を加えた正方形の Y 側のデータ。 -/
lemma UnitCommaFiberSquare.precomp_target (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) (i : B ⟶ A) :
    (s.precomp i).target = ((Δ[1] : SSet.{u}) ◁ i) ≫ s.target := by
  have hs := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare.target s.family_square
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (i ≫ s.family)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget_precomp]
  exact congrArg (fun f ↦ (Δ[1] : SSet.{u}) ◁ i ≫ f) hs

/-- 概要：パラメータ制限の coherence は元の円柱の射の前合成。
方針：区間の展開と fiber のホモトピーの前合成自然性を使う。
規約：ホモトピーの端点の輸送は raw な射を変えない。
使われ方：関手正方形の前合成の検査。 -/
lemma UnitCommaFiberSquare.precomp_coherence (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) (i : B ⟶ A) :
    (s.precomp i).coherence.h = (((Δ[1] : SSet.{u}) ◁ i) ▷ (Δ[1] : SSet.{u})) ≫ s.coherence.h := by
  have hs := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A ↦ t.coherence.h) s.family_square
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (i ≫ s.family))).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy_precomp]
  exact congrArg (fun f ↦ (((Δ[1] : SSet.{u}) ◁ i) ▷ (Δ[1] : SSet.{u})) ≫ f) hs

/-- 概要：関手正方形の表示はパラメータ前合成と厳密に可換。
方針：coherence の制限公式と座標の並べ替えの自然性を使う。
規約：正方形全体の図式の等式。
使われ方：時間端点で元の正方形を回収する。 -/
lemma UnitCommaFiberSquare.precomp_functorSquare (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A) (i : B ⟶ A) :
    (s.precomp i).functorSquare = s.functorSquare ≫ (pre i).app X := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  change uncurry (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder B ≫ (s.precomp i).coherence.h)) =
    (i ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1])) ≫ uncurry (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder A ≫ s.coherence.h))
  rw [uncurry_curry, uncurry_curry, s.precomp_coherence]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder B ≫ (((Δ[1] : SSet.{u}) ◁ i) ▷ (Δ[1] : SSet.{u})) =
      (i ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1])) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder A := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hc, Category.assoc]

/-- 概要：comma 正方形は標的と関手正方形の図式で決まる。
方針：curry の単射性と並べ替えの逆で coherence の射を回収する。
規約：ホモトピー類でなく元の図式を比較する。
使われ方：時間端点から元の正方形・族を回収する。 -/
lemma UnitCommaFiberSquare.ext_functorSquare {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A}
    (ht : s.target = t.target) (hQ : s.functorSquare = t.functorSquare) : s = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare.ext ht
  have h := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.commaSquareUnreorder A ≫ uncurry f) hQ
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare.functorSquare, uncurry_curry, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.commaSquareUnreorder_reorder, Category.id_comp] using h

end

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
