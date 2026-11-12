module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFinitePushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：二点鎖上の simplicial replacement の写像円柱表示に使う射と端点の計算。
方針：底の nerve を標準 1 単体へ移し、末尾の一点の係数値を回収する。
規約：底の二点鎖を ULift (Fin 2) とする。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、Proposition 5.2.4.5（Tag 024R）、1 単体上の scaffold の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：二点鎖の係数図式の唯一の非恒等な構造射。
方針：零から一への順序射を係数関手で写す。
規約：端点は ULift.up 0 と ULift.up 1。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、写像円柱に入る係数の射。 -/
def scaffoldIntervalMap (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    F.obj (ULift.up 0) ⟶ F.obj (ULift.up 1) :=
  F.map (homOfLE (show (ULift.up (0 : Fin 2) : ULift.{u} _) ≤ ULift.up 1 from by decide))

/-- 概要：二点鎖の simplicial replacement の最初の係数部分を prism として表示する。
方針：標準 1 単体と有限順序の nerve の同型に最初の係数の組み立て射を合成する。
規約：係数図式の充填性は不要。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、写像円柱の円柱部分からの標準射。 -/
noncomputable def scaffoldIntervalPrism (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F :=
  (stdSimplex.isoNerve.{u} 1).hom ▷ F.obj (ULift.up 0) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial 1)

/-- 概要：一点の末尾の標準包含を全体へ戻すと終端係数の標準包含になる。
方針：末尾の零頂点が全体の一頂点に写ることを定義から計算する。
規約：係数単体はそのまま保つ。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、写像円柱の終域部分の同定。 -/
lemma scaffoldIntervalTail_constantLift (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0 ⋙ F) (ULift.up 0) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0) F =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F (ULift.up 1) := rfl

/-- 概要：一点の末尾への組み立て射は二点鎖の係数の構造射に一致する。
方針：一点の底上の組み立て射の計算に始対象からの構造射を代入する。
規約：第一射影で底の一点を忘れ、F(0)→F(1) を適用する。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、写像円柱の貼り合わせの係数射。 -/
lemma scaffoldIntervalTail_assembly (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial 1))) =
    snd (nerve (ULift.{u} (Fin 1))) (F.obj (ULift.up 0)) ≫ scaffoldIntervalMap F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0 ⋙ F) (ULift.up 0) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly_point (ULift.up (0 : Fin 1))
    (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial 1)))
  exact h

/-- 概要：末尾の nerve の包含は標準 1 単体の終端の prism 包含に対応する。
方針：各次数の底の一点の射列の頂点が零であることを使い、後者写像の像を一に同定する。
規約：係数の単体は第二成分として保存される。
使われ方：Kerodon Example 5.3.2.13（Tag 0366）、写像円柱の貼り合わせの端点射。 -/
lemma scaffoldIntervalTail_endpoint (K : SSet.{u}) :
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail 0) ▷ K) ≫ (stdSimplex.isoNerve.{u} 1).inv ▷ K =
      snd (nerve (ULift.{u} (Fin 1))) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  refine Prod.ext ?_ (by rfl)
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (σ.obj i).down.val + 1 = 1
  have hi := (σ.obj i).down.isLt
  omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
