module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldNerveFirstEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFinitePushout

/-!
概要：有限鎖の最初の辺と尾部を用いた simplicial replacement の拡張。
方針：係数付きの nerve の比較を尾部の replacement に沿って pushout する。
規約：通常の単体集合の pushout のみを使い、係数の Kan 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、scaffold 比較の有限次元の帰納段階。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：最初の辺の係数付き部分を尾部の replacement に貼った対象。
方針：辺と尾部の nerve の pushout と F(0) の積に、尾部の組み立て射を貼る。
規約：共通部分は尾部の nerve と F(0) の積。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、小さい円柱部分から全体への比較の始域。 -/
noncomputable def scaffoldFiniteExtension (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) : SSet.{u} :=
  pushout
    (pushout.inr (stdSimplex.δ (0 : Fin 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ▷ F.obj (ULift.up 0))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)))))

/-- 概要：最初の辺と尾部を貼った対象から有限鎖の全 replacement への射。
方針：係数付き nerve の比較と尾部の包含を pushout の普遍性で貼る。
規約：区間部分は初期係数の組み立て射で全体へ写す。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、全体比較の帰納段階の射。 -/
noncomputable def scaffoldFiniteExtensionMap (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    scaffoldFiniteExtension n F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F :=
  pushout.desc
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ▷ F.obj (ULift.up 0)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) F) (by
      rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inr]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteReplacement_isPushout n F).w.symm)

/-- 概要：有限鎖の拡張射は係数付き nerve の比較の pushout。
方針：尾部と初期係数による全体の分解から、左側の pushout を消去する。
規約：上辺は nerve の比較と F(0) の積。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、inner anodyne 性を全体の比較へ移す正方形。 -/
lemma scaffoldFiniteExtensionMap_isPushout (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ▷ F.obj (ULift.up 0))
      (pushout.inl
        (pushout.inr (stdSimplex.δ (0 : Fin 2))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ▷ F.obj (ULift.up 0))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)))
      (scaffoldFiniteExtensionMap n F) := by
  let a := pushout.inr (stdSimplex.δ (0 : Fin 2))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ▷ F.obj (ULift.up 0)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))))
  have hp : IsPushout (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n ▷ F.obj (ULift.up 0))) b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)))
      (pushout.inr a b ≫ scaffoldFiniteExtensionMap n F) := by
    rw [scaffoldFiniteExtensionMap, pushout.inr_desc]
    dsimp only [a]
    rw [← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inr]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteReplacement_isPushout n F).flip
  exact hp.of_left (by rw [scaffoldFiniteExtensionMap, pushout.inl_desc])
    (IsPushout.of_hasPushout a b)

/-- 概要：最初の辺と尾部から全 replacement への拡張は inner anodyne。
方針：係数付き nerve の比較の inner anodyne 性を pushout で移す。
規約：係数値の Kan 性も矢の同値性も仮定しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、scaffold の全体比較の帰納法。 -/
lemma scaffoldFiniteExtensionMap_innerAnodyne (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    innerAnodyneExtensions (scaffoldFiniteExtensionMap n F) :=
  MorphismProperty.of_isPushout (scaffoldFiniteExtensionMap_isPushout n F).flip
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_whiskerRight_innerAnodyne n (F.obj (ULift.up 0)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
